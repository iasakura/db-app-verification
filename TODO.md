# TODO

## High priority
- [ ] Replace placeholder proof `sorry` for refinement preservation:
  - `DbAppVerification/Examples/ApprovalAuth/Refinement.lean:107`
  - Prove `preservation : Preservation tsB tsA Ref` (step + query preservation against DSL semantics).

## Medium priority
- [ ] Add focused tests for new SQLDSL syntax macros (`join`, `from ... using ... where ... select ...`, `dsl{...}`).
- [ ] Consider replacing ad-hoc decrease proof in `evalQuery` filtering branch with a cleaner well-founded helper lemma for readability.

## Notes
- [ ] `lake build` currently succeeds, but emits a warning due to the `sorry` above.
