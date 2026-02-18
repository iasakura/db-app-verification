import Std
import DbAppVerification.Examples.ApprovalAuth.Spec

namespace DbAppVerification
namespace Postgres
namespace Encode

open Examples.ApprovalAuth

structure BoundSql where
  sql : String
  params : Array String
  deriving Repr

private def hasToken (sql token : String) : Bool :=
  (sql.splitOn token).length > 1

private def replaceToken (sql token replacement : String) : String :=
  String.intercalate replacement (sql.splitOn token)

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

private def natS (n : Nat) : String :=
  toString n

def cmdNamedParams : Cmd → List (String × String)
  | .Employ e => [ ("eid", natS e) ]
  | .AddManager m e => [ ("key", s!"{m}:{e}"), ("mid", natS m), ("eid", natS e) ]
  | .NewDocument did => [ ("did", natS did) ]
  | .AddHistory did hid doc => [ ("hkey", s!"{did}:{hid}"), ("did", natS did), ("hid", natS hid), ("doc", doc) ]
  | .Propose sender target did hid pid =>
      [ ("from", natS sender), ("to", natS target), ("did", natS did), ("hid", natS hid), ("pid", natS pid) ]
  | .Accept actor pid =>
      [ ("by", natS actor), ("pid", natS pid) ]
  | .Reject actor pid comment =>
      [ ("by", natS actor), ("pid", natS pid), ("comment", comment) ]

def queryNamedParams : Q → List (String × String)
  | .AcceptedProposalFrom sender pid => [ ("from", natS sender), ("pid", natS pid) ]

private def assertPrefix : String :=
  "-- ASSERT "

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

def splitStatements (sql : String) : List String :=
  (sql.splitOn ";\n").filterMap fun part =>
    let t := part.trim
    if t.isEmpty then none else some t

end Encode
end Postgres
end DbAppVerification
