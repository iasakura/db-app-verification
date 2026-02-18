import Std
import DbAppVerification.Framework.SQLDSL.Core

namespace DbAppVerification
namespace Framework

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
