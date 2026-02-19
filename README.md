# db-app-verification

An experimental Lean 4 repository that combines:

- refinement verification between an abstract model `A` and an implementation model `B`
- deterministic artifact generation (SQL / HTTP stubs) from a SQL-ish DSL

## What This Project Provides

- A general verification framework based on `TransitionSystem`
  - step preservation (forward simulation)
  - query preservation (observational equivalence)
  - a soundness theorem over finite command traces
- A deliberately restricted SQL DSL
  - AST (deep embedding)
  - interpreter over an in-memory DB
  - SQL pretty-printer
  - deterministic non-executing artifact generation (DDL / handler SQL / HTTP stubs)
- A concrete Approval/Auth workflow example
  - abstract spec: `Spec`
  - DB implementation: `DBImpl`
  - refinement link: `Refinement`
- PostgreSQL binding (Lean FFI) and smoke tests

## Repository Layout (Key Files)

- `DbAppVerification/Framework/Core.lean`
  - `TransitionSystem`, `Preservation`, `soundness`
- `DbAppVerification/Framework/DB.lean`
  - in-memory DB model (`Value`, `Row`, `Table`, `DB`)
- `DbAppVerification/Framework/SQLDSL/Core.lean`
  - SQL DSL AST and operational semantics
- `DbAppVerification/Framework/SQLDSL/Syntax.lean`
  - DSL macros/operators (`dsl{...}`, `from ... select ...`, `===`, `&&&`, etc.)
- `DbAppVerification/Framework/SQLDSL/Emit.lean`
  - SQL/DDL/HTTP stub emitters
- `DbAppVerification/Framework/SQLDSLPostgres.lean`
  - execution bridge between SQLDSL and the Postgres binding
- `DbAppVerification/Examples/ApprovalAuth/Spec.lean`
  - abstract spec (`tsA`)
- `DbAppVerification/Examples/ApprovalAuth/DBImpl.lean`
  - DSL implementation (`tsB`)
- `DbAppVerification/Examples/ApprovalAuth/Refinement.lean`
  - abstraction function `abs`, relation `Refinement`, refinement theorem
- `Main.lean`
  - print/export DDL+SQL artifacts and run Postgres smoke checks

## Setup

Requirements:

- Lean / Lake (version from `lean-toolchain`)
- `g++` (for FFI C++ build)
- PostgreSQL development headers (e.g. `libpq-dev` on Debian/Ubuntu)
- Optional: Docker (for `scripts/test_pg_binding.sh`)

Build:

```bash
lake build
```

## Usage

Print DDL / handler SQL / HTTP stubs:

```bash
lake exe db-app-verification
```

Export artifacts into a directory:

```bash
lake exe db-app-verification --emit-dir generated
```

Generated files:

- `generated/schema.sql`
- `generated/handlers/*.sql`
- `generated/http_stubs.json`

`generated/` is already ignored via `.gitignore`.

## Postgres Binding Smoke Tests

Direct:

```bash
lake exe db-app-verification --pg-test "postgresql://postgres:postgres@127.0.0.1:5432/postgres"
```

Docker-based smoke test:

```bash
bash scripts/test_pg_binding.sh
```

This script starts a `postgres:16` container and verifies that `SELECT 1` succeeds.

## DSL Syntax (Excerpt)

`SQLDSL/Syntax.lean` provides notation such as:

```lean
from "proposals"
  using
    [
      join "decisions" on "proposals.pid" == "decisions.pid",
      join "histories" on "proposals.did" == "histories.did"
    ]
  where
    ((.col "proposals.pid" === .param "pid") &&&
     (.col "proposals.from" === .param "from"))
  select ["histories.doc"]
```

```lean
dsl{
  assertMsg (existsBy "employees" (.col "eid" === .param "from")) "notEmployed";
  .insert "proposals" (.param "pid") [("pid", .param "pid")]
}
```

## Current Status

- `lake build` succeeds.
- `preservation : Preservation tsB tsA Refinement` in
  `DbAppVerification/Examples/ApprovalAuth/Refinement.lean`
  is still a `sorry`.
- Open items are tracked in `TODO.md`.

## Acknowledgements

- PostgreSQL Lean FFI integration in this repo is adapted from:
  - https://github.com/aripiprazole/pgsql
  - Source files used as implementation base: `Pgsql/FFI.lean`, `pgsql/ffi.cpp`

The current codebase modifies API shape, runtime wiring, and error handling, but the external-object + `libpq` FFI structure is directly derived from the repository above.

Note: at the time of integration, the upstream repository did not include a top-level `LICENSE` file in the cloned tree. Please add explicit licensing confirmation before external distribution.
