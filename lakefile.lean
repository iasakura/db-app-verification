import Lake
open System Lake DSL

package «db-app-verification» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

lean_lib DbAppVerification where

@[default_target]
lean_exe «db-app-verification» where
  root := `Main

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "DbAppVerification" / "postgres" / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "DbAppVerification" / "postgres" / "ffi.cpp"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", "/usr/include/postgresql"
  ]
  buildO oFile srcJob weakArgs #["-fPIC", "-std=c++17"] "g++" getLeanTrace

extern_lib libdbappffi pkg := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "dbappffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]
