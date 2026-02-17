# db-app-verification

Lean4 framework and examples for state-machine refinement plus SQL-ish DSL extraction.

## Acknowledgements
- PostgreSQL Lean FFI integration in this repo is adapted from:
  - https://github.com/aripiprazole/pgsql
  - Source files used as implementation base: `Pgsql/FFI.lean`, `pgsql/ffi.cpp`

The current codebase modifies API shape, runtime wiring, and error handling, but the external-object + `libpq` FFI structure is directly derived from the repository above.

Note: at the time of integration, the upstream repository did not include a top-level `LICENSE` file in the cloned tree. Please add explicit licensing confirmation before external distribution.
