import Std
import DbAppVerification.Framework.SQLDSL
import DbAppVerification.Framework.SQLDSLPostgres
import DbAppVerification.Examples.ApprovalAuth.Spec
import DbAppVerification.Examples.ApprovalAuth.DBImpl
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

private def mapRuntimeErr : Framework.SQLDSLPostgres.RuntimeErr → Err
  | .unknownHandler _ => .constraintViolation
  | .pg e => mapPgErr e

/-- Execute one command in one SQL transaction using emitted handler SQL. -/
def execCommandTx (conn : Connection) (cmd : Cmd) : IO (Except Err Unit) := do
  match (← Framework.SQLDSLPostgres.execHandlerTxNamed conn handlers (cmdTag cmd) (cmdNamedParams cmd)) with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error (mapRuntimeErr e))

private def rowDoc? (row : RowData) : Option String :=
  match row.cols.get? "histories.doc" with
  | some (some s) => some s
  | _ =>
      match row.cols.get? "doc" with
      | some (some s) => some s
      | _ => none

def queryAcceptedFromPg (conn : Connection) (q : Q) : IO (Except Err R) := do
  match (← Framework.SQLDSLPostgres.execQueryNamed conn acceptedDocQuery (queryNamedParams q)) with
  | .error e =>
      pure (.error (mapRuntimeErr e))
  | .ok [] =>
      pure (.ok none)
  | .ok (row :: _) =>
      pure (.ok (rowDoc? row))

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
