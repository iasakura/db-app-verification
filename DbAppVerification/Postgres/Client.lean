import Std
import Std.Sync.Mutex
import DbAppVerification.Postgres.FFI

namespace DbAppVerification
namespace Postgres

open IO

structure PgConfig where
  conninfo : String
  deriving Repr

structure Connection where
  raw : RawConn
  mutex : Std.BaseMutex

inductive PgErr where
  | connectError (message : String)
  | sqlError (message : String)
  | decodeError (message : String)
  | txError (message : String)
  deriving Repr, DecidableEq

structure RowData where
  cols : Std.HashMap String (Option String)
  deriving Repr

private def withLock (mutex : Std.BaseMutex) (act : IO α) : IO α := do
  mutex.lock
  try
    let res ← act
    mutex.unlock
    pure res
  catch e =>
    mutex.unlock
    throw e

def connect (cfg : PgConfig) : IO (Except PgErr Connection) := do
  try
    match (← connectRaw cfg.conninfo) with
    | .ok raw =>
        let mutex ← Std.BaseMutex.new
        pure (.ok { raw := raw, mutex := mutex })
    | .error msg =>
        pure (.error (.connectError msg))
  catch e =>
    pure (.error (.connectError e.toString))

/-- Raw connection object is finalized by GC (FFI external class finalizer). -/
def close (_conn : Connection) : IO Unit :=
  pure ()

def exec (conn : Connection) (sql : String) (params : Array String) : IO (Except PgErr Unit) := do
  try
    let res ← withLock conn.mutex (execRaw conn.raw sql params)
    match res with
    | .commandOk => pure (.ok ())
    | .tuples _ => pure (.ok ())
    | .error msg => pure (.error (.sqlError msg))
  catch e =>
    pure (.error (.sqlError e.toString))

def query (conn : Connection) (sql : String) (params : Array String) : IO (Except PgErr (List RowData)) := do
  try
    let res ← withLock conn.mutex (execRaw conn.raw sql params)
    match res with
    | .error msg =>
        pure (.error (.sqlError msg))
    | .commandOk =>
        pure (.ok [])
    | .tuples result =>
        let rows := resultRowsRaw result
        let cols := resultColsRaw result
        let mut out : List RowData := []
        for rowIx in [0:rows.toNat] do
          let mut rowMap : Std.HashMap String (Option String) := {}
          for colIx in [0:cols.toNat] do
            let name := resultColNameRaw result colIx.toUSize
            let value := resultValueRaw result rowIx.toUSize colIx.toUSize
            rowMap := rowMap.insert name value
          out := out.concat { cols := rowMap }
        pure (.ok out)
  catch e =>
    pure (.error (.sqlError e.toString))

end Postgres
end DbAppVerification
