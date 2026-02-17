import Std
import DbAppVerification.Framework.SQLDSL
import DbAppVerification.Postgres.Client

namespace DbAppVerification
namespace Framework
namespace SQLDSLPostgres

open Postgres

structure BoundSql where
  sql : String
  params : Array String
  deriving Repr

inductive RuntimeErr where
  | unknownHandler (cmdTag : String)
  | pg (err : PgErr)
  deriving Repr, DecidableEq

private def hasToken (sql token : String) : Bool :=
  (sql.splitOn token).length > 1

private def replaceToken (sql token replacement : String) : String :=
  String.intercalate replacement (sql.splitOn token)

/-- Convert named `:param` placeholders into positional `$1, $2, ...`. -/
def bindNamedParams (sql : String) (named : List (String × String)) : BoundSql :=
  named.foldl
    (fun acc (name, value) =>
      let token := s!":{name}"
      if hasToken acc.sql token then
        let idx := acc.params.size + 1
        {
          sql := replaceToken acc.sql token s!"${idx}"
          params := acc.params.push value
        }
      else
        acc)
    { sql := sql, params := #[] }

private def assertPrefix : String :=
  "-- ASSERT "

/-- Rewrite SQLDSL assert-emission into a Postgres-failing expression. -/
def rewriteAssertToPostgres (stmt : String) : String :=
  match stmt.splitOn "\n" with
  | header :: _ =>
      if header.startsWith assertPrefix then
        let msg := (header.drop assertPrefix.length).trim
        stmt.replace s!"RAISE(FAIL, '{msg}')" s!"CAST('ERR:{msg}' AS INTEGER)"
      else
        stmt
  | [] =>
      stmt

/-- Split emitted statement sequence by the `emitStmtSQL` separator convention. -/
def splitStatements (sql : String) : List String :=
  (sql.splitOn ";\n").filterMap fun part =>
    let t := part.trim
    if t.isEmpty then none else some t

private def encodeValueParam : Value → String
  | .int i => toString i
  | .str s => s
  | .bool true => "true"
  | .bool false => "false"

private def insertSortedByName (x : String × String) : List (String × String) → List (String × String)
  | [] => [x]
  | y :: ys =>
      if compare x.1 y.1 == Ordering.lt then x :: y :: ys else y :: insertSortedByName x ys

private def sortNamed (xs : List (String × String)) : List (String × String) :=
  xs.foldl (fun acc x => insertSortedByName x acc) []

/-- Deterministic conversion from param map to named SQL params. -/
def namedParamsOfEnv (params : ParamEnv) : List (String × String) :=
  sortNamed (params.toList.map (fun (k, v) => (k, encodeValueParam v)))

private def rollbackIgnore (conn : Connection) : IO Unit := do
  let _ ← Postgres.exec conn "ROLLBACK" #[]
  pure ()

private def execOneStatement
    (conn : Connection)
    (stmt : String)
    (named : List (String × String)) : IO (Except RuntimeErr Unit) := do
  let stmtPg := rewriteAssertToPostgres stmt
  let bound := bindNamedParams stmtPg named
  match (← Postgres.exec conn bound.sql bound.params) with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error (.pg e))

private partial def execStatements
    (conn : Connection)
    (stmts : List String)
    (named : List (String × String)) : IO (Except RuntimeErr Unit) := do
  match stmts with
  | [] =>
      pure (.ok ())
  | stmt :: rest =>
      match (← execOneStatement conn stmt named) with
      | .error e => pure (.error e)
      | .ok _ => execStatements conn rest named

private def commitOrRollback (conn : Connection) (res : Except RuntimeErr Unit) : IO (Except RuntimeErr Unit) := do
  match res with
  | .error e =>
      rollbackIgnore conn
      pure (.error e)
  | .ok _ =>
      match (← Postgres.exec conn "COMMIT" #[]) with
      | .ok _ => pure (.ok ())
      | .error e =>
          rollbackIgnore conn
          pure (.error (.pg e))

/-- Execute an emitted SQLDSL handler inside one SQL transaction. -/
def execHandlerTxNamed
    (conn : Connection)
    (handlers : Handler)
    (cmdTag : String)
    (named : List (String × String)) : IO (Except RuntimeErr Unit) := do
  match (← Postgres.exec conn "BEGIN" #[]) with
  | .error e =>
      pure (.error (.pg e))
  | .ok _ =>
      match emitHandlerSQL handlers cmdTag with
      | .error _ =>
          rollbackIgnore conn
          pure (.error (.unknownHandler cmdTag))
      | .ok sql =>
          let stmts := splitStatements sql
          let bodyRes ← execStatements conn stmts named
          commitOrRollback conn bodyRes

/-- Execute an emitted SQLDSL handler using `ParamEnv` values. -/
def execHandlerTx
    (conn : Connection)
    (handlers : Handler)
    (cmdTag : String)
    (params : ParamEnv) : IO (Except RuntimeErr Unit) :=
  execHandlerTxNamed conn handlers cmdTag (namedParamsOfEnv params)

/-- Execute a DSL query via Postgres binding with named parameters. -/
def execQueryNamed
    (conn : Connection)
    (q : Query)
    (named : List (String × String)) : IO (Except RuntimeErr (List RowData)) := do
  let bound := bindNamedParams (emitQuerySQL q) named
  match (← Postgres.query conn bound.sql bound.params) with
  | .ok rows => pure (.ok rows)
  | .error e => pure (.error (.pg e))

/-- Execute a DSL query via Postgres binding with map parameters. -/
def execQuery
    (conn : Connection)
    (q : Query)
    (params : ParamEnv := {}) : IO (Except RuntimeErr (List RowData)) :=
  execQueryNamed conn q (namedParamsOfEnv params)

end SQLDSLPostgres
end Framework
end DbAppVerification
