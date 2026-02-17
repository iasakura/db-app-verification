import Std

namespace DbAppVerification
namespace Framework

inductive Value where
  | int : Int → Value
  | str : String → Value
  | bool : Bool → Value
  deriving Repr, DecidableEq, BEq, Hashable, Ord

abbrev Row := Std.HashMap String Value
abbrev Table := Std.HashMap Value Row
abbrev DB := Std.HashMap String Table

inductive DBErr where
  | missingTable (table : String)
  | duplicateKey (table : String) (pk : Value)
  | missingKey (table : String) (pk : Value)
  | missingColumn (col : String)
  | typeMismatch (msg : String)
  | constraintViolation (msg : String)
  deriving Repr, DecidableEq

namespace DB

def empty : DB := {}

def emptyTable : Table := {}

private def getTable (db : DB) (table : String) : Except DBErr Table :=
  match db.get? table with
  | some t => .ok t
  | none => .error (.missingTable table)

private def setTable (db : DB) (table : String) (t : Table) : DB :=
  Std.HashMap.insert db table t

private def insertSortedByKey (x : Value × Row) : List (Value × Row) → List (Value × Row)
  | [] => [x]
  | y :: ys =>
      if compare x.1 y.1 == Ordering.lt then
        x :: y :: ys
      else
        y :: insertSortedByKey x ys

private def sortPairsByKey (xs : List (Value × Row)) : List (Value × Row) :=
  xs.foldl (fun acc x => insertSortedByKey x acc) []

def insert (db : DB) (table : String) (pk : Value) (row : Row) : Except DBErr DB := do
  let t ← getTable db table
  match t.get? pk with
  | some _ => .error (.duplicateKey table pk)
  | none =>
      let t' := Std.HashMap.insert t pk row
      pure (setTable db table t')

def delete (db : DB) (table : String) (pk : Value) : Except DBErr DB := do
  let t ← getTable db table
  match t.get? pk with
  | none => .error (.missingKey table pk)
  | some _ =>
      let t' := t.erase pk
      pure (setTable db table t')

def update (db : DB) (table : String) (pk : Value) (f : Row → Except DBErr Row) : Except DBErr DB := do
  let t ← getTable db table
  let row ←
    match t.get? pk with
    | some r => pure r
    | none => .error (.missingKey table pk)
  let row' ← f row
  let t' := Std.HashMap.insert t pk row'
  pure (setTable db table t')

def selectOne (db : DB) (table : String) (pk : Value) : Except DBErr (Option Row) := do
  let t ← getTable db table
  pure (t.get? pk)

def selectMany (db : DB) (table : String) (pred : Row → Bool) : Except DBErr (List (Value × Row)) := do
  let t ← getTable db table
  let pairs := t.toList.filter (fun (_, row) => pred row)
  pure (sortPairsByKey pairs)

/-- Ensure all tables from schema names exist (empty if absent). -/
def ensureTables (db : DB) (tableNames : List String) : DB :=
  tableNames.foldl
    (fun acc name =>
      match acc.get? name with
      | some _ => acc
      | none => Std.HashMap.insert acc name emptyTable)
    db

end DB

end Framework
end DbAppVerification
