# ApprovalAuth Refinement Checklist

This file is a working checklist for proving:

- `preservation : Preservation tsB tsA Refinement`

## A. Hard Gate: Counterexample-First

- [ ] Before any proof edits, search for counterexamples against current relation/candidate invariants.
- [ ] If any counterexample exists, report it first (state + command/query + mismatch).
- [ ] Do not continue proof construction until the counterexample is addressed by design updates.

Reference counterexample (already found for weak relation):

- [x] Weak relation `Refinement b a := abs b = a` admits malformed DB rows and breaks `step_error_align`.

## B. Naming and Relation Design

- [ ] Keep relation name as `Refinement` (do not use `Ref` alias).
- [ ] Define app-side invariant name as `ImplementationInvariant` (not `RefInv`/`BizInv`).
- [ ] Target relation:
  - [ ] `Refinement b a := abs b = a ∧ ImplementationInvariant b`
- [ ] Keep theorem statement shape unchanged:
  - [ ] `theorem preservation : Preservation tsB tsA Refinement := ...`

## C. Framework/State Layer Assumptions (Already Introduced)

- [x] `InvariantState` is class-based (`inv : State → Prop`), not dependent-pair proof in the state payload.
- [x] `TransitionSystem` carries `stateInvariant` instance.
- [x] `Preservation` requires:
  - [x] `refinement_inv_impl : Refinement b a -> stateInv b`
  - [x] `refinement_inv_abs : Refinement b a -> stateInv a`
- [x] `SB = DBState approvalSchema` and integrity is enforced by `execHandlerSafe` / `DBState.ofDB?`.

## D. Define ImplementationInvariant (ApprovalAuth-specific only)

Define these predicates in `Refinement.lean`:

- [ ] `ManagersInvariant b`
- [ ] `ProposalsInvariant b`
- [ ] `DecisionsInvariant b`
- [ ] `CrossTableInvariant b`
- [ ] `ImplementationInvariant b := ManagersInvariant b ∧ ProposalsInvariant b ∧ DecisionsInvariant b ∧ CrossTableInvariant b`

Keep out of this layer (Framework responsibility):

- [x] PK-row canonical consistency
- [x] composite PK consistency for `histories` (`(did,hid)`)

## E. Preservation Obligation Order (Top-level)

From `constructor` on `Preservation`:

- [ ] `refinement_inv_impl`
- [ ] `refinement_inv_abs`
- [ ] `step_success`
- [ ] `step_error_align`
- [ ] `query_preserve`

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

- [ ] `lean_diagnostic_messages` for touched files
- [ ] `lake env lean DbAppVerification/Examples/ApprovalAuth/Refinement.lean`
- [ ] `lake build`
- [ ] Confirm only expected warning remains until `sorry` is removed

## K. Final Exit Criteria

- [ ] `preservation` has no `sorry`
- [ ] `approval_refinement_sound` compiles unchanged
- [ ] `lake build` succeeds with no new warnings/errors beyond accepted baseline
