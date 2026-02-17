import Std

namespace DbAppVerification
namespace Framework

structure ExportArtifacts where
  ddl : String
  handlers : List (String × String)
  httpStubs : String
  deriving Repr

structure ExportPaths where
  rootDir : System.FilePath
  schemaFile : System.FilePath := "schema.sql"
  handlersDir : System.FilePath := "handlers"
  httpStubsFile : System.FilePath := "http_stubs.json"
  deriving Repr

def defaultExportPaths (rootDir : System.FilePath) : ExportPaths :=
  { rootDir := rootDir }

private def sanitizeTag (tag : String) : String :=
  String.mk <| tag.toList.map fun c =>
    if c.isAlphanum || c = '-' || c = '_' then c else '_'

private def insertSortedByTag (x : String × String) : List (String × String) → List (String × String)
  | [] => [x]
  | y :: ys =>
      if compare x.1 y.1 == Ordering.lt then x :: y :: ys else y :: insertSortedByTag x ys

private def sortHandlersByTag (handlers : List (String × String)) : List (String × String) :=
  handlers.foldl (fun acc h => insertSortedByTag h acc) []

/-- Write extracted artifacts deterministically into the given output tree. -/
def writeArtifacts (paths : ExportPaths) (artifacts : ExportArtifacts) : IO Unit := do
  IO.FS.createDirAll paths.rootDir

  let schemaPath := paths.rootDir / paths.schemaFile
  IO.FS.writeFile schemaPath artifacts.ddl

  let handlersPath := paths.rootDir / paths.handlersDir
  let handlersExists ← handlersPath.pathExists
  if handlersExists then
    let isDir ← handlersPath.isDir
    if isDir then
      IO.FS.removeDirAll handlersPath
  IO.FS.createDirAll handlersPath

  for (tag, sql) in sortHandlersByTag artifacts.handlers do
    let fileName := sanitizeTag tag ++ ".sql"
    IO.FS.writeFile (handlersPath / fileName) sql

  let stubsPath := paths.rootDir / paths.httpStubsFile
  IO.FS.writeFile stubsPath artifacts.httpStubs

end Framework
end DbAppVerification
