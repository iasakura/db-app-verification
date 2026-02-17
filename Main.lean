import DbAppVerification

open DbAppVerification.Examples.ApprovalAuth

def printHandlerSQL : IO Unit := do
  for (tag, sql) in emitHandlerSQLStrings do
    IO.println s!"-- {tag}"
    IO.println sql
    IO.println ""

def main : IO Unit := do
  IO.println "== ApprovalAuth DDL =="
  IO.println emitDDLString
  IO.println ""
  IO.println "== ApprovalAuth Handler SQL =="
  printHandlerSQL
  IO.println "== ApprovalAuth HTTP Stubs =="
  IO.println emitHTTPStubsString
