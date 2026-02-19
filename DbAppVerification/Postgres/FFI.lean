namespace DbAppVerification
namespace Postgres

-- Attribution:
-- This module is adapted from https://github.com/aripiprazole/pgsql
-- (notably Pgsql/FFI.lean), then modified for this project's API/runtime.

open IO

opaque Nonempty : NonemptyType

def RawConn : Type := Nonempty.type

def RawResult : Type := Nonempty.type

inductive ConnectResult where
  | ok (conn : RawConn)
  | error (message : String)

inductive ExecResult where
  | commandOk
  | tuples (result : RawResult)
  | error (message : String)

@[extern "lean_dbapp_pg_initialize"]
opaque initPostgres : IO Unit

builtin_initialize initPostgres

@[extern "lean_dbapp_pg_connect"]
opaque connectRaw : String → IO ConnectResult

@[extern "lean_dbapp_pg_exec"]
opaque execRaw : (@& RawConn) → String → Array String → IO ExecResult

@[extern "lean_dbapp_pg_result_rows"]
opaque resultRowsRaw : (@& RawResult) → USize

@[extern "lean_dbapp_pg_result_cols"]
opaque resultColsRaw : (@& RawResult) → USize

@[extern "lean_dbapp_pg_result_col_name"]
opaque resultColNameRaw : (@& RawResult) → USize → String

@[extern "lean_dbapp_pg_result_value"]
opaque resultValueRaw : (@& RawResult) → USize → USize → Option String

end Postgres
end DbAppVerification
