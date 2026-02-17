import DbAppVerification

open DbAppVerification.Framework
open DbAppVerification.Examples.ApprovalAuth

private def printHandlerSQL : IO Unit := do
  for (tag, sql) in emitHandlerSQLStrings do
    IO.println s!"-- {tag}"
    IO.println sql
    IO.println ""

private def printStdoutArtifacts : IO Unit := do
  IO.println "== ApprovalAuth DDL =="
  IO.println emitDDLString
  IO.println ""
  IO.println "== ApprovalAuth Handler SQL =="
  printHandlerSQL
  IO.println "== ApprovalAuth HTTP Stubs =="
  IO.println emitHTTPStubsString

private def writeArtifactFiles (dir : String) : IO Unit := do
  let paths := defaultExportPaths (System.FilePath.mk dir)
  writeArtifacts paths approvalArtifacts
  IO.println s!"wrote artifacts to: {dir}"
  IO.println s!"- {dir}/schema.sql"
  IO.println s!"- {dir}/handlers/*.sql"
  IO.println s!"- {dir}/http_stubs.json"

private def printUsage : IO Unit := do
  IO.println "Usage:"
  IO.println "  db-app-verification"
  IO.println "  db-app-verification --emit-dir <dir>"
  IO.println "  db-app-verification --pg-test <conninfo>"

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      printStdoutArtifacts
  | ["--emit-dir", dir] =>
      writeArtifactFiles dir
  | ["--pg-test", conninfo] =>
      match (← pgSmokeTestValue conninfo) with
      | .ok v => IO.println s!"postgres smoke test: ok (one={v})"
      | .error e =>
          IO.eprintln s!"postgres smoke test failed: {e}"
  | _ =>
      printUsage
