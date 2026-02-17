import Std
import DbAppVerification.Framework.DB

namespace DbAppVerification
namespace Framework

inductive ColType where
  | int
  | string
  | bool
  deriving Repr, DecidableEq

structure Column where
  name : String
  ty : ColType
  nullable : Bool := false
  deriving Repr, DecidableEq

structure ForeignKey where
  col : String
  refTable : String
  refCol : String
  deriving Repr, DecidableEq

structure TableDecl where
  name : String
  pkCol : String
  columns : List Column
  fks : List ForeignKey := []
  deriving Repr, DecidableEq

structure Schema where
  tables : List TableDecl
  deriving Repr, DecidableEq

abbrev ParamEnv := Std.HashMap String Value
abbrev QueryRows := List Row

structure EvalEnv where
  params : ParamEnv := {}
  lets : Std.HashMap String QueryRows := {}
  deriving Repr

structure JoinSpec where
  table : String
  leftRef : String
  rightRef : String
  deriving Repr, DecidableEq

mutual
  inductive Expr where
    | lit : Value → Expr
    | col : String → Expr
    | param : String → Expr
    | letCol : String → Nat → String → Expr
    deriving Repr

  inductive Pred where
    | eq : Expr → Expr → Pred
    | and : Pred → Pred → Pred
    | or : Pred → Pred → Pred
    | not : Pred → Pred
    | exists : Query → Pred
    deriving Repr

  structure Query where
    baseTable : String
    joins : List JoinSpec := []
    where? : Option Pred := none
    project : List String
    deriving Repr
end

inductive Stmt where
  | insert : String → Expr → List (String × Expr) → Stmt
  | deleteWhere : String → String → Pred → Stmt
  | updateWhereSet : String → String → Pred → List (String × Expr) → Stmt
  | assert : Pred → String → Stmt
  | seq : Stmt → Stmt → Stmt
  | letQ : String → Query → Stmt → Stmt
  | return : Expr → Stmt
  deriving Repr

abbrev Handler := Std.HashMap String Stmt

inductive ExecErr where
  | db : DBErr → ExecErr
  | unknownHandler : String → ExecErr
  | missingParam : String → ExecErr
  | missingColumn : String → ExecErr
  | missingLetBinding : String → ExecErr
  | badIndex : String → Nat → ExecErr
  | assertFailed : String → ExecErr
  | invalidProgram : String → ExecErr
  deriving Repr

private def liftDB {α} (x : Except DBErr α) : Except ExecErr α :=
  x.mapError ExecErr.db

private def getRowCol (row : Row) (name : String) : Except ExecErr Value :=
  match row.get? name with
  | some v => .ok v
  | none => .error (.missingColumn name)

private def qualifyRow (table : String) (row : Row) : Row :=
  row.fold (init := row) fun acc k v =>
    acc.insert s!"{table}.{k}" v

private def mergeRow (a b : Row) : Row :=
  b.fold (init := a) fun acc k v => acc.insert k v

private def sortedRows (db : DB) (table : String) : Except ExecErr (List (Value × Row)) :=
  liftDB (DB.selectMany db table (fun _ => true))

mutual
  partial def evalExpr (env : EvalEnv) (ctx : Row) : Expr → Except ExecErr Value
    | .lit v => pure v
    | .col name => getRowCol ctx name
    | .param name =>
        match env.params.get? name with
        | some v => pure v
        | none => .error (.missingParam name)
    | .letCol binding idx col =>
        match env.lets.get? binding with
        | none => .error (.missingLetBinding binding)
        | some rows =>
            match rows[idx]? with
            | none => .error (.badIndex binding idx)
            | some row => getRowCol row col

  partial def evalPred (db : DB) (env : EvalEnv) (ctx : Row) : Pred → Except ExecErr Bool
    | .eq e1 e2 => do
        let v1 ← evalExpr env ctx e1
        let v2 ← evalExpr env ctx e2
        pure (v1 = v2)
    | .and p q => do
        let b1 ← evalPred db env ctx p
        if b1 then
          evalPred db env ctx q
        else
          pure false
    | .or p q => do
        let b1 ← evalPred db env ctx p
        if b1 then
          pure true
        else
          evalPred db env ctx q
    | .not p => do
        let b ← evalPred db env ctx p
        pure (!b)
    | .exists q => do
        let rows ← evalQuery db env q
        pure (!rows.isEmpty)

  partial def evalQuery (db : DB) (env : EvalEnv) (q : Query) : Except ExecErr (List Row) := do
    let base ← sortedRows db q.baseTable
    let initCtxs : List Row := base.map (fun (_, row) => qualifyRow q.baseTable row)

    let joined ←
      q.joins.foldlM
        (fun acc join => do
          let rhs ← sortedRows db join.table
          let rhsRows := rhs.map (fun (_, row) => qualifyRow join.table row)
          let mut out : List Row := []
          for leftCtx in acc do
            for rightCtx in rhsRows do
              let lv ← getRowCol leftCtx join.leftRef
              let rv ← getRowCol rightCtx join.rightRef
              if lv = rv then
                out := out.concat (mergeRow leftCtx rightCtx)
          pure out)
        initCtxs

    let filtered ←
      match q.where? with
      | none => pure joined
      | some p =>
          joined.foldlM
            (fun acc row => do
              let ok ← evalPred db env row p
              if ok then
                pure (acc.concat row)
              else
                pure acc)
            []

    filtered.foldlM
      (fun acc row => do
        let projected :=
          q.project.foldl
            (fun proj name =>
              match row.get? name with
              | some v => proj.insert name v
              | none => proj)
            ({} : Row)
        pure (acc.concat projected))
      []
end

partial def execStmt (schema : Schema) (stmt : Stmt) (env : EvalEnv) (db : DB) : Except ExecErr (DB × EvalEnv) := do
  match stmt with
  | .insert table pkExpr cols =>
      let pk ← evalExpr env {} pkExpr
      let row ←
        cols.foldlM
          (fun acc (name, e) => do
            let v ← evalExpr env {} e
            pure (acc.insert name v))
          ({} : Row)
      let db' ← liftDB (DB.insert db table pk row)
      pure (db', env)
  | .deleteWhere table _pkCol pred =>
      let rows ← sortedRows db table
      let mut dbCur := db
      for (pk, row) in rows do
        let ctx := qualifyRow table row |>.fold (init := row) fun acc k v => acc.insert k v
        let shouldDel ← evalPred dbCur env ctx pred
        if shouldDel then
          dbCur ← liftDB (DB.delete dbCur table pk)
      pure (dbCur, env)
  | .updateWhereSet table _pkCol pred sets =>
      let rows ← sortedRows db table
      let mut dbCur := db
      for (pk, row) in rows do
        let ctx0 := qualifyRow table row |>.fold (init := row) fun acc k v => acc.insert k v
        let shouldUpd ← evalPred dbCur env ctx0 pred
        if shouldUpd then
          let row' ←
            sets.foldlM
              (fun r (name, e) => do
                let v ← evalExpr env ctx0 e
                pure (r.insert name v))
              row
          dbCur ← liftDB (DB.update dbCur table pk (fun _ => .ok row'))
      pure (dbCur, env)
  | .assert pred msg =>
      let ok ← evalPred db env {} pred
      if ok then
        pure (db, env)
      else
        .error (.assertFailed msg)
  | .seq s1 s2 => do
      let (db1, env1) ← execStmt schema s1 env db
      execStmt schema s2 env1 db1
  | .letQ name q body => do
      let rows ← evalQuery db env q
      let env' := { env with lets := env.lets.insert name rows }
      execStmt schema body env' db
  | .return _ =>
      pure (db, env)

private def tableNames (schema : Schema) : List String :=
  schema.tables.map (·.name)

def execHandler (schema : Schema) (handlers : Handler)
    (cmdTag : String) (params : ParamEnv) (db : DB) : Except ExecErr DB := do
  let stmt ←
    match handlers.get? cmdTag with
    | some s => pure s
    | none => .error (.unknownHandler cmdTag)
  let db0 := DB.ensureTables db (tableNames schema)
  let env0 : EvalEnv := { params := params }
  let (db1, _) ← execStmt schema stmt env0 db0
  pure db1

private def emitColType : ColType → String
  | .int => "INTEGER"
  | .string => "TEXT"
  | .bool => "BOOLEAN"

private def emitColumn (col : Column) : String :=
  let nullPart := if col.nullable then "" else " NOT NULL"
  s!"{col.name} {emitColType col.ty}{nullPart}"

private def emitFK (fk : ForeignKey) : String :=
  s!"FOREIGN KEY ({fk.col}) REFERENCES {fk.refTable}({fk.refCol})"

private def emitTableDDL (t : TableDecl) : String :=
  let cols := t.columns.map emitColumn
  let pk := s!"PRIMARY KEY ({t.pkCol})"
  let fks := t.fks.map emitFK
  let all := cols ++ [pk] ++ fks
  s!"CREATE TABLE {t.name} (\n  {String.intercalate ",\n  " all}\n);"

def emitDDL (schema : Schema) : String :=
  String.intercalate "\n\n" (schema.tables.map emitTableDDL)

private def emitValue : Value → String
  | .int i => toString i
  | .str s => s!"'{s}'"
  | .bool b => if b then "TRUE" else "FALSE"

private partial def emitExpr : Expr → String
  | .lit v => emitValue v
  | .col c => c
  | .param p => s!":{p}"
  | .letCol name idx col => s!"${name}[{idx}].{col}"

mutual
  private partial def emitPred : Pred → String
    | .eq a b => s!"({emitExpr a} = {emitExpr b})"
    | .and p q => s!"({emitPred p} AND {emitPred q})"
    | .or p q => s!"({emitPred p} OR {emitPred q})"
    | .not p => s!"(NOT {emitPred p})"
    | .exists q => s!"EXISTS ({emitQuerySQLAux q})"

  private partial def emitJoin (j : JoinSpec) : String :=
    s!"JOIN {j.table} ON {j.leftRef} = {j.rightRef}"

  private partial def emitQuerySQLAux (q : Query) : String :=
    let selectPart :=
      if q.project.isEmpty then "*" else String.intercalate ", " q.project
    let joinPart :=
      if q.joins.isEmpty then ""
      else " " ++ String.intercalate " " (q.joins.map emitJoin)
    let wherePart :=
      match q.where? with
      | none => ""
      | some p => s!" WHERE {emitPred p}"
    s!"SELECT {selectPart} FROM {q.baseTable}{joinPart}{wherePart}"
end

def emitQuerySQL (q : Query) : String :=
  emitQuerySQLAux q

partial def emitStmtSQL : Stmt → String
  | .insert table pk cols =>
      let names := ("pk" :: cols.map (·.1))
      let values := (emitExpr pk :: cols.map (fun c => emitExpr c.2))
      s!"INSERT INTO {table} ({String.intercalate ", " names}) VALUES ({String.intercalate ", " values})"
  | .deleteWhere table _pk pred =>
      s!"DELETE FROM {table} WHERE {emitPred pred}"
  | .updateWhereSet table _pk pred sets =>
      let setPart :=
        sets.map (fun (name, e) => s!"{name} = {emitExpr e}") |>
          String.intercalate ", "
      s!"UPDATE {table} SET {setPart} WHERE {emitPred pred}"
  | .assert pred msg =>
      s!"-- ASSERT {msg}\nSELECT CASE WHEN {emitPred pred} THEN 1 ELSE RAISE(FAIL, '{msg}') END"
  | .seq s1 s2 =>
      s!"{emitStmtSQL s1};\n{emitStmtSQL s2}"
  | .letQ name q body =>
      s!"-- LET {name} AS ({emitQuerySQL q})\n{emitStmtSQL body}"
  | .return e =>
      s!"-- RETURN {emitExpr e}"

def emitHandlerSQL (handlers : Handler) (cmdTag : String) : Except ExecErr String := do
  let stmt ←
    match handlers.get? cmdTag with
    | some s => pure s
    | none => .error (.unknownHandler cmdTag)
  pure (emitStmtSQL stmt)

private def insertSortedString (x : String) : List String → List String
  | [] => [x]
  | y :: ys =>
      if compare x y == Ordering.lt then x :: y :: ys else y :: insertSortedString x ys

private def sortedHandlerTags (handlers : Handler) : List String :=
  (handlers.toList.map (·.1)).foldl (fun acc x => insertSortedString x acc) []

/-- Deterministic JSON-ish HTTP handler stubs emitted from handler keys. -/
def emitHTTPStubs (handlers : Handler) : String :=
  let entries :=
    sortedHandlerTags handlers |>.map (fun tag =>
      s!"  method=POST path=/api/{tag} handler={tag}")
  "[\n" ++ String.intercalate ",\n" entries ++ "\n]"

end Framework
end DbAppVerification
