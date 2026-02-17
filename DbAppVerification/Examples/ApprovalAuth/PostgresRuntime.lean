import Std
import DbAppVerification.Framework.SQLDSL
import DbAppVerification.Examples.ApprovalAuth.SpecA
import DbAppVerification.Examples.ApprovalAuth.ImplB
import DbAppVerification.Postgres.Client
import DbAppVerification.Postgres.Encode

namespace DbAppVerification
namespace Examples
namespace ApprovalAuth

open Framework
open Postgres
open Postgres.Encode

private def containsText (s needle : String) : Bool :=
  (s.splitOn needle).length > 1

private def mapSqlErr (msg : String) : Err :=
  if containsText msg "ERR:notEmployed" then .notEmployed
  else if containsText msg "ERR:notManager" then .notManager
  else if containsText msg "ERR:missingDoc" then .missingDoc
  else if containsText msg "ERR:missingHistory" then .missingHistory
  else if containsText msg "ERR:missingProposal" then .missingProposal
  else if containsText msg "ERR:alreadyDecided" then .alreadyDecided
  else if containsText msg "ERR:unauthorized" then .unauthorized
  else .constraintViolation

private def mapPgErr : PgErr → Err
  | .sqlError msg => mapSqlErr msg
  | .connectError _ => .constraintViolation
  | .decodeError _ => .constraintViolation
  | .txError _ => .constraintViolation

private def execStatement (conn : Connection) (stmt : String) (named : List (String × String)) : IO (Except Err Unit) := do
  let stmtPg := rewriteAssertToPostgres stmt
  let bound := bindNamedParams stmtPg named
  match (← Postgres.exec conn bound.sql bound.params) with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error (mapPgErr e))

private def rollbackIgnore (conn : Connection) : IO Unit := do
  let _ ← Postgres.exec conn "ROLLBACK" #[]
  pure ()

private def commitOrRollback (conn : Connection) (res : Except Err Unit) : IO (Except Err Unit) := do
  match res with
  | .error e =>
      rollbackIgnore conn
      pure (.error e)
  | .ok _ =>
      match (← Postgres.exec conn "COMMIT" #[]) with
      | .ok _ => pure (.ok ())
      | .error e =>
          rollbackIgnore conn
          pure (.error (mapPgErr e))

private partial def execStatements
    (conn : Connection)
    (stmts : List String)
    (named : List (String × String)) : IO (Except Err Unit) := do
  match stmts with
  | [] =>
      pure (.ok ())
  | stmt :: rest =>
      match (← execStatement conn stmt named) with
      | .error e => pure (.error e)
      | .ok _ => execStatements conn rest named

/-- Execute one command in one SQL transaction using emitted handler SQL. -/
def execCommandTx (conn : Connection) (cmd : Cmd) : IO (Except Err Unit) := do
  match (← Postgres.exec conn "BEGIN" #[]) with
  | .error e =>
      pure (.error (mapPgErr e))
  | .ok _ =>
      let handlerSql :=
        match emitHandlerSQL handlers (cmdTag cmd) with
        | .ok sql => some sql
        | .error _ => none
      match handlerSql with
      | none =>
          rollbackIgnore conn
          pure (.error .constraintViolation)
      | some sql =>
          let named := cmdNamedParams cmd
          let stmts := splitStatements sql
          let bodyRes ← execStatements conn stmts named
          commitOrRollback conn bodyRes

private def acceptedFromQuerySql : String :=
  "SELECT h.doc AS doc FROM proposals p JOIN decisions d ON p.pid = d.pid JOIN histories h ON p.did = h.did AND p.hid = h.hid WHERE p.pid = :pid AND p.\"from\" = :from AND d.kind = 'accept' LIMIT 1"

def queryAcceptedFromPg (conn : Connection) (q : Q) : IO (Except Err R) := do
  let bound := bindNamedParams acceptedFromQuerySql (queryNamedParams q)
  match (← Postgres.query conn bound.sql bound.params) with
  | .error e =>
      pure (.error (mapPgErr e))
  | .ok [] =>
      pure (.ok none)
  | .ok (row :: _) =>
      match row.cols.get? "doc" with
      | some (some s) => pure (.ok (some s))
      | _ => pure (.ok none)

def stepBPG (conn : Connection) (cmd : Cmd) : IO (Except Err Unit) :=
  execCommandTx conn cmd

def queryBPG (conn : Connection) (q : Q) : IO (Except Err R) :=
  queryAcceptedFromPg conn q

def pgSmokeTestValue (conninfo : String) : IO (Except String String) := do
  match (← Postgres.connect { conninfo := conninfo }) with
  | .error e =>
      pure (.error s!"connect failed: {repr e}")
  | .ok conn =>
      let res ← Postgres.query conn "SELECT 1 AS one" #[]
      Postgres.close conn
      match res with
      | .error e =>
          pure (.error s!"query failed: {repr e}")
      | .ok [] =>
          pure (.error "query returned no rows")
      | .ok (row :: _) =>
          match row.cols.get? "one" with
          | some (some v) =>
              if v = "1" then
                pure (.ok v)
              else
                pure (.error s!"unexpected value for one: {v}")
          | _ =>
              pure (.error "column 'one' missing or NULL")

def pgSmokeTest (conninfo : String) : IO (Except String Unit) := do
  match (← pgSmokeTestValue conninfo) with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error e)

end ApprovalAuth
end Examples
end DbAppVerification
