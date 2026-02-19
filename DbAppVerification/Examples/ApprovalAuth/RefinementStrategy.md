# ApprovalAuth Refinement Checklist

This file is a working checklist for proving:

- `preservation : Preservation tsB tsA Refinement`

## A. Hard Gate: Counterexample-First

- [x] Before any proof edits, search for counterexamples against current relation/candidate invariants.
- [x] If any counterexample exists, report it first (state + command/query + mismatch).
- [x] Do not continue proof construction until the counterexample is addressed by design updates.

Reference counterexample (already found for weak relation):

- [x] Weak relation `Refinement b a := abs b = a` admits malformed DB rows and breaks `step_error_align`.
- [x] State with missing required manager columns (`mid`/`eid`) gave
  `dbIntegrity = true`, `stepB(AddManager 1 2) = error constraintViolation`,
  `stepA(abs b)(AddManager 1 2) = ok`.
  This is now addressed by strengthening Framework `dbIntegrity` to check row/column shape and column types.
- [x] Even with strengthened `dbIntegrity`, stateInv-only relation still has counterexample:
  `managers` row `(\"key\"=\"x\", \"mid\"=1, \"eid\"=2)` gives
  `dbIntegrity = true`, `stepB(AddManager 1 2) = ok`,
  `stepA(abs b)(AddManager 1 2) = error constraintViolation`.
  This is now addressed by schema update: `managers` PK is `(mid,eid)` (no synthetic `key` column).
- [x] Non-PK typedness mismatch counterexample:
  proposal row with `pid=7` but `to=-1` gives
  `dbIntegrity = true`, `stepB(Accept 0 7) = unauthorized`,
  `stepA(abs b)(Accept 0 7) = missingProposal`.
  This is addressed by `ProposalsInvariant` (all proposal ID fields parse as Nat and references are well-formed).
- [x] Non-PK enum-domain mismatch counterexample:
  decision row with `kind=\"oops\"` gives
  `dbIntegrity = true`, `stepB(Accept actor pid) = alreadyDecided`,
  `stepA(abs b)(Accept actor pid) = ok` (decision row dropped by abstraction parser).
  This is addressed by `DecisionsInvariant` (decision rows must parse to `DecisionKind`).

## B. Naming and Relation Design

- [x] Keep relation name as `Refinement` (do not use `Ref` alias).
- [x] Define app-side invariant name as `ImplementationInvariant` (not `RefInv`/`BizInv`).
- [x] Target relation:
  - [x] `Refinement b a := abs b = a ∧ ImplementationInvariant b`
- [x] Keep theorem statement shape unchanged:
  - [x] `theorem preservation : Preservation tsB tsA Refinement := ...`

PK-specific audit (unnecessary PK introduces extra app invariants):

- [x] `employees`: no synthetic PK; abstract key uses `eid`.
- [x] `managers`: synthetic `key` removed; PK changed to `(mid,eid)`.
- [x] `documents`: no synthetic PK; abstract key uses `did`.
- [x] `histories`: composite PK `(did,hid)` matches abstract key.
- [x] `proposals`: PK `pid` matches abstract key.
- [x] `decisions`: PK `pid` matches abstract key.
- [x] No remaining table requires app-specific invariants solely to restore synthetic PK consistency.

## C. Framework/State Layer Assumptions (Already Introduced)

- [x] `InvariantState` is class-based (`inv : State → Prop`), not dependent-pair proof in the state payload.
- [x] `TransitionSystem` carries `stateInvariant` instance.
- [x] `Preservation` requires:
  - [x] `refinement_inv_impl : Refinement b a -> stateInv b`
  - [x] `refinement_inv_abs : Refinement b a -> stateInv a`
- [x] `SB = DBState approvalSchema` and integrity is enforced by `execHandlerSafe` / `DBState.ofDB?`.
- [x] `dbIntegrity` now checks not only PK canonicality but also row/column shape + value type consistency against schema.
- [x] Proof ergonomics: `cmdParams` and `mapExecErr` are public in `DBImpl.lean` so command-case proofs can unfold them directly.

## D. Define ImplementationInvariant (ApprovalAuth-specific only)

Define these predicates in `Refinement.lean`:

- [x] `ManagersInvariant b`
  - current content: `True` (covered by Framework `stateInv` after managers PK switched to `(mid,eid)`).
- [x] `ProposalsInvariant b`
  - current content: every proposal row references employed sender/target, existing manager relation, existing doc/history pair.
- [x] `DecisionsInvariant b`
  - current content: every decision row references existing proposal and `by` matches proposal target.
- [ ] `CrossTableInvariant b` (currently placeholder `True`)
- [x] `ImplementationInvariant b := stateInv b ∧ ManagersInvariant b ∧ ProposalsInvariant b ∧ DecisionsInvariant b ∧ CrossTableInvariant b`

Keep out of this layer (Framework responsibility):

- [x] PK-row canonical consistency
- [x] composite PK consistency for `histories` (`(did,hid)`)

## E. Preservation Obligation Order (Top-level)

From `constructor` on `Preservation`:

- [x] `refinement_inv_impl`
- [x] `refinement_inv_abs`
- [ ] `step_success`
- [ ] `step_error_align`
- [ ] `query_preserve`

Current mechanization status:

- [x] `step_success`: command split (`cases c`) is in place in `Refinement.lean`.
- [x] `step_error_align`: command split (`cases c`) is in place in `Refinement.lean`.
- [x] `query_preserve`: query split (`cases q`) is in place in `Refinement.lean`.
- [x] `step_success`: each command now has an explicit `case ...` block (`Employ`..`Reject`) instead of `all_goals`.
- [x] `step_error_align`: each command now has an explicit `case ...` block (`Employ`..`Reject`) instead of `all_goals`.

## F. Lemma Backlog

### F1. Parsing/Row helpers

- [ ] `natOfValue?_eq_some_iff`
- [ ] `rowNat?_eq_some_iff_get_int_nonneg`
- [ ] `rowStr?_eq_some_iff_get_str`
- [ ] `parseDecisionKind_sound`

### F2. Abstraction fold helpers

- [ ] `absEmployed_insert_wf`
- [ ] `absManagers_insert_wf`
- [ ] `absDocuments_insert_wf`
- [ ] `absHistories_insert_wf`
- [ ] `absProposals_insert_wf`
- [ ] `absDecisions_insert_wf`

### F3. ImplementationInvariant preservation

- [ ] `implementationInvariant_preserved_employ`
- [ ] `implementationInvariant_preserved_addManager`
- [ ] `implementationInvariant_preserved_newDocument`
- [ ] `implementationInvariant_preserved_addHistory`
- [ ] `implementationInvariant_preserved_propose`
- [ ] `implementationInvariant_preserved_accept`
- [ ] `implementationInvariant_preserved_reject`

### F4. Error alignment

- [ ] `error_align_employ`
- [ ] `error_align_addManager`
- [ ] `error_align_newDocument`
- [ ] `error_align_addHistory`
- [ ] `error_align_propose`
- [ ] `error_align_accept`
- [ ] `error_align_reject`

### F5. Query bridge

- [ ] `acceptedDocQuery_rows_characterization`
- [ ] `queryB_eq_queryA_of_refinement`

## G. Command-by-command Proof Loop

Run this loop for each command `Cmd`:

- [ ] Unfold `tsB.step` / `stepB` / `execHandlerSafe` (and local DSL stmt).
- [ ] Unfold `tsA.step` / `stepA`.
- [ ] Use `Refinement -> stateInv` and `ImplementationInvariant` facts to align guards.
- [ ] Prove success simulation branch.
- [ ] Prove error-alignment branch.
- [ ] Prove post-state `ImplementationInvariant` preservation.

Commands to complete:

- [ ] `Employ`
- [ ] `AddManager`
- [ ] `NewDocument`
- [ ] `AddHistory`
- [ ] `Propose`
- [ ] `Accept`
- [ ] `Reject`

## H. Query Preservation Checklist

For `AcceptedProposalFrom sender pid`:

- [ ] Show SQL-side join/filter conditions correspond to abstract-side lookup conditions.
- [ ] Use histories composite-key uniqueness (from Framework integrity) to get functional `(did,hid)` lookup.
- [ ] Conclude `queryB b q = queryA a q` under `Refinement b a`.

## I. Initial-State Invariant Clarification

- [x] No separate `Inv b0` argument is needed in `soundness`.
- [x] `hRefinement0 : Refinement b0 a0` plus `refinement_inv_*` obligations already force initial invariants.

## J. Validation Loop (Every Milestone)

- [x] `lean_diagnostic_messages` for touched files
- [x] `lake env lean DbAppVerification/Examples/ApprovalAuth/Refinement.lean`
- [x] `lake build`
- [x] Confirm only expected warning remains until `sorry` is removed

## K. Final Exit Criteria

- [ ] `preservation` has no `sorry`
- [ ] `approval_refinement_sound` compiles unchanged
- [ ] `lake build` succeeds with no new warnings/errors beyond accepted baseline
