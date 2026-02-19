import Std
import DbAppVerification.Framework.DB
import DbAppVerification.Framework.Core

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
  pkCols : List String := []
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

private def findTableDecl? (schema : Schema) (table : String) : Option TableDecl :=
  schema.tables.foldl
    (fun acc t => if t.name = table then some t else acc)
    none

private def encodePkPart : Value → String
  | .int i => s!"i:{i}"
  | .str s => s!"s:{s.length}:{s}"
  | .bool b => if b then "b:1" else "b:0"

private def compositePkValue (row : Row) (pkCols : List String) : Except ExecErr Value := do
  let parts ←
    pkCols.foldlM
      (fun acc col => do
        let v ← getRowCol row col
        pure (acc.concat (encodePkPart v)))
      ([] : List String)
  pure (.str ("cmp:" ++ String.intercalate "|" parts))

private def insertPkValue (schema : Schema) (table : String) (row : Row) (pkFromStmt : Value) :
    Except ExecErr Value := do
  match findTableDecl? schema table with
  | none => pure pkFromStmt
  | some t =>
      if t.pkCols.isEmpty then
        pure pkFromStmt
      else
        compositePkValue row t.pkCols

private def expectedPkOfRow? (t : TableDecl) (row : Row) : Option Value :=
  if t.pkCols.isEmpty then
    row.get? t.pkCol
  else
    match compositePkValue row t.pkCols with
    | .ok pk => some pk
    | .error _ => none

private def tableIntegrity (t : TableDecl) (table : Table) : Bool :=
  (table.toList.all fun (entry : Value × Row) =>
    match expectedPkOfRow? t entry.2 with
    | some pk => pk == entry.1
    | none => false)

private def tableIntegrityInDB (db : DB) (t : TableDecl) : Bool :=
  match db.get? t.name with
  | none => true
  | some table => tableIntegrity t table

def dbIntegrity (schema : Schema) (db : DB) : Bool :=
  schema.tables.all (tableIntegrityInDB db)

structure DBState (schema : Schema) where
  db : DB

instance (schema : Schema) : DbAppVerification.Framework.InvariantState (DBState schema) where
  inv := fun s => dbIntegrity schema s.db

def DBState.empty (schema : Schema) : DBState schema :=
  { db := {} }

def DBState.ofDB? (schema : Schema) (db : DB) : Except ExecErr (DBState schema) :=
  if dbIntegrity schema db then
    .ok { db := db }
  else
    .error (.invalidProgram "integrityViolation")

private def ensureDBStateIntegrity (schema : Schema) (db : DBState schema) : Except ExecErr Unit :=
  if dbIntegrity schema db.db then
    .ok ()
  else
    .error (.invalidProgram "integrityViolation")

def evalExpr (env : EvalEnv) (ctx : Row) (e : Expr) : Except ExecErr Value :=
  match e with
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

mutual
  def evalPred (db : DB) (env : EvalEnv) (ctx : Row) (p : Pred) : Except ExecErr Bool :=
    match p with
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
  termination_by sizeOf p

  def evalQuery (db : DB) (env : EvalEnv) (q : Query) : Except ExecErr (List Row) := do
      let base ← sortedRows db q.baseTable
      let initCtxs : List Row := base.map (fun (_, row) => qualifyRow q.baseTable row)

      let joined ←
        q.joins.foldlM
          (fun acc j => do
            let rhs ← sortedRows db j.table
            let rhsRows := rhs.map (fun (_, row) => qualifyRow j.table row)
            let mut out : List Row := []
            for leftCtx in acc do
              for rightCtx in rhsRows do
                let lv ← getRowCol leftCtx j.leftRef
                let rv ← getRowCol rightCtx j.rightRef
                if lv = rv then
                  out := out.concat (mergeRow leftCtx rightCtx)
            pure out)
          initCtxs

      let filtered ←
        match h : q.where? with
        | none => pure joined
        | some p =>
            joined.foldlM
              (fun acc row => do
                have h : sizeOf p < sizeOf q := by
                  obtain ⟨ _ ⟩ := q
                  subst h; simp
                  omega
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
  termination_by sizeOf q
end

def execStmt (schema : Schema) (stmt : Stmt) (env : EvalEnv) (db : DB) : Except ExecErr (DB × EvalEnv) := do
  match stmt with
  | .insert table pkExpr cols =>
      let pkFromStmt ← evalExpr env {} pkExpr
      let row ←
        cols.foldlM
          (fun acc (name, e) => do
            let v ← evalExpr env {} e
            pure (acc.insert name v))
          ({} : Row)
      let pk ← insertPkValue schema table row pkFromStmt
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

def execHandlerSafe (schema : Schema) (handlers : Handler)
    (cmdTag : String) (params : ParamEnv) (db : DBState schema) : Except ExecErr (DBState schema) := do
  let _ ← ensureDBStateIntegrity schema db
  let db1 ← execHandler schema handlers cmdTag params db.db
  DBState.ofDB? schema db1

end Framework
end DbAppVerification
