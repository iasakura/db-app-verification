import Std
import DbAppVerification.Framework.Core
import DbAppVerification.Framework.DB
import DbAppVerification.Examples.ApprovalAuth.Spec
import DbAppVerification.Examples.ApprovalAuth.DBImpl

namespace DbAppVerification
namespace Examples
namespace ApprovalAuth

open Framework

private def tableOrEmpty (db : DB) (name : String) : Table :=
  match db.get? name with
  | some t => t
  | none => {}

private def natOfValue? : Value → Option Nat
  | .int i =>
      if i < 0 then none else some i.toNat
  | _ => none

private def stringOfValue? : Value → Option String
  | .str s => some s
  | _ => none

private def rowNat? (row : Row) (col : String) : Option Nat :=
  row.get? col >>= natOfValue?

private def rowStr? (row : Row) (col : String) : Option String :=
  row.get? col >>= stringOfValue?

private def absEmployed (db : DB) : Std.HashSet EmployeeId :=
  (tableOrEmpty db "employees").toList.foldl
    (fun acc (_, row) =>
      match rowNat? row "eid" with
      | some e => acc.insert e
      | none => acc)
    {}

private def absManagers (db : DB) : Std.HashSet (EmployeeId × EmployeeId) :=
  (tableOrEmpty db "managers").toList.foldl
    (fun acc (_, row) =>
      match rowNat? row "mid", rowNat? row "eid" with
      | some m, some e => acc.insert (m, e)
      | _, _ => acc)
    {}

private def absDocuments (db : DB) : Std.HashSet DocumentId :=
  (tableOrEmpty db "documents").toList.foldl
    (fun acc (_, row) =>
      match rowNat? row "did" with
      | some did => acc.insert did
      | none => acc)
    {}

private def absHistories (db : DB) : Std.HashMap (DocumentId × HistoryId) Doc :=
  (tableOrEmpty db "histories").toList.foldl
    (fun acc (_, row) =>
      match rowNat? row "did", rowNat? row "hid", rowStr? row "doc" with
      | some did, some hid, some doc => acc.insert (did, hid) doc
      | _, _, _ => acc)
    {}

private def absProposals (db : DB) : Std.HashMap ProposalId (EmployeeId × EmployeeId × DocumentId × HistoryId) :=
  (tableOrEmpty db "proposals").toList.foldl
    (fun acc (_, row) =>
      match rowNat? row "pid", rowNat? row "from", rowNat? row "to", rowNat? row "did", rowNat? row "hid" with
      | some pid, some sender, some target, some did, some hid =>
          acc.insert pid (sender, target, did, hid)
      | _, _, _, _, _ => acc)
    {}

private def parseDecisionKind (row : Row) : Option DecisionKind :=
  match rowStr? row "kind" with
  | some "accept" => some .accept
  | some "reject" =>
      let comment :=
        match rowStr? row "comment" with
        | some c => c
        | none => ""
      some (.reject comment)
  | _ => none

private def absDecisions (db : DB) : Std.HashMap ProposalId (EmployeeId × DecisionKind) :=
  (tableOrEmpty db "decisions").toList.foldl
    (fun acc (_, row) =>
      match rowNat? row "pid", rowNat? row "by", parseDecisionKind row with
      | some pid, some actor, some k => acc.insert pid (actor, k)
      | _, _, _ => acc)
    {}

/-- Abstraction from implementation DB state to abstract model state. -/
def abs (db : SB) : SA :=
  {
    employed := absEmployed db.db
    manager := absManagers db.db
    docExists := absDocuments db.db
    histContent := absHistories db.db
    proposals := absProposals db.db
    decision := absDecisions db.db
  }

private def natV (n : Nat) : Value :=
  .int (Int.ofNat n)

private def employeeExists (db : DB) (eid : Nat) : Bool :=
  (tableOrEmpty db "employees").contains (natV eid)

private def documentExists (db : DB) (did : Nat) : Bool :=
  (tableOrEmpty db "documents").contains (natV did)

private def managerRelExists (db : DB) (m : Nat) (e : Nat) : Bool :=
  (tableOrEmpty db "managers").toList.any fun (_, row) =>
    rowNat? row "mid" == some m &&
      rowNat? row "eid" == some e

private def historyExists (db : DB) (did : Nat) (hid : Nat) : Bool :=
  (tableOrEmpty db "histories").toList.any fun (_, row) =>
    rowNat? row "did" == some did &&
      rowNat? row "hid" == some hid

private def proposalTargetOfPid? (db : DB) (pid : Nat) : Option Nat :=
  match (tableOrEmpty db "proposals").get? (natV pid) with
  | some row => rowNat? row "to"
  | none => none

private def proposalRowValid (db : DB) (row : Row) : Bool :=
  match rowNat? row "pid", rowNat? row "from", rowNat? row "to", rowNat? row "did", rowNat? row "hid" with
  | some _pid, some sender, some target, some did, some hid =>
      employeeExists db sender &&
        employeeExists db target &&
        managerRelExists db target sender &&
        documentExists db did &&
        historyExists db did hid
  | _, _, _, _, _ => false

private def proposalsWellFormed (db : DB) : Bool :=
  (tableOrEmpty db "proposals").toList.all fun (_, row) =>
    proposalRowValid db row

private def decisionRowValid (db : DB) (row : Row) : Bool :=
  match rowNat? row "pid", rowNat? row "by", parseDecisionKind row with
  | some pid, some actor, some _kind =>
      match proposalTargetOfPid? db pid with
      | some target => actor == target
      | none => false
  | _, _, _ => false

private def decisionsWellFormed (db : DB) : Bool :=
  (tableOrEmpty db "decisions").toList.all fun (_, row) =>
    decisionRowValid db row

def managersInvariantB (_b : SB) : Bool :=
  true

def proposalsInvariantB (b : SB) : Bool :=
  proposalsWellFormed b.db

def decisionsInvariantB (b : SB) : Bool :=
  decisionsWellFormed b.db

def crossTableInvariantB (_b : SB) : Bool :=
  true

def ManagersInvariant (b : SB) : Prop :=
  managersInvariantB b = true

def ProposalsInvariant (b : SB) : Prop :=
  proposalsInvariantB b = true

def DecisionsInvariant (b : SB) : Prop :=
  decisionsInvariantB b = true

def CrossTableInvariant (b : SB) : Prop :=
  crossTableInvariantB b = true

/-- Implementation-side invariant used by ApprovalAuth refinement. -/
def ImplementationInvariant (b : SB) : Prop :=
  stateInv b ∧
    ManagersInvariant b ∧
    ProposalsInvariant b ∧
    DecisionsInvariant b ∧
    CrossTableInvariant b

/-- Refinement relation from SQL-side state to abstract state. -/
abbrev Refinement : SB → SA → Prop :=
  fun b a => And (RefOfAbs abs b a) (ImplementationInvariant b)

theorem refinement_abs_eq {b : SB} {a : SA} (h : Refinement b a) : abs b = a :=
  h.1

theorem refinement_impl_inv {b : SB} {a : SA} (h : Refinement b a) : ImplementationInvariant b :=
  h.2

theorem refinement_state_inv_impl {b : SB} {a : SA} (h : Refinement b a) : stateInv b :=
  (refinement_impl_inv h).1

theorem refinement_state_inv_abs {b : SB} {a : SA} (_h : Refinement b a) : stateInv a := by
  trivial

/-- TODO: mechanize command and query preservation against DSL semantics. -/
theorem preservation : Preservation tsB tsA Refinement := by
  refine
    {
      refinement_inv_impl := ?_
      refinement_inv_abs := ?_
      step_success := ?_
      step_error_align := ?_
      query_preserve := ?_
    }
  · intro b a hRefinement
    exact refinement_state_inv_impl hRefinement
  · intro b a _hRefinement
    exact refinement_state_inv_abs _hRefinement
  · intro b a c b' hRefinement hStepB
    have hAbs : abs b = a := refinement_abs_eq hRefinement
    subst hAbs
    cases c <;> simp [tsB, tsA, stepB, stepA, cmdTag] at hStepB ⊢
    case Employ e =>
      sorry
    case AddManager m e =>
      sorry
    case NewDocument did =>
      sorry
    case AddHistory did hid doc =>
      sorry
    case Propose sender target did hid pid =>
      sorry
    case Accept actor pid =>
      sorry
    case Reject actor pid comment =>
      sorry
  · intro b a c eB hRefinement hStepB
    have hAbs : abs b = a := refinement_abs_eq hRefinement
    subst hAbs
    cases c <;> simp [tsB, tsA, stepB, stepA, cmdTag] at hStepB ⊢
    case Employ e =>
      sorry
    case AddManager m e =>
      sorry
    case NewDocument did =>
      sorry
    case AddHistory did hid doc =>
      sorry
    case Propose sender target did hid pid =>
      sorry
    case Accept actor pid =>
      sorry
    case Reject actor pid comment =>
      sorry
  · intro b a q hRefinement
    have hAbs : abs b = a := refinement_abs_eq hRefinement
    subst hAbs
    cases q with
    | AcceptedProposalFrom sender pid =>
        simp [tsB, tsA, queryB, queryA]
        sorry

theorem approval_refinement_sound
    {b0 : tsB.State} {a0 : tsA.State} {cmds : List Cmd} {bN : tsB.State}
    (hRefinement0 : Refinement b0 a0)
    (hRunB : tsB.run b0 cmds = .ok bN) :
    ∃ aN, tsA.run a0 cmds = .ok aN ∧ Refinement bN aN ∧
      ∀ q, tsB.query bN q = tsA.query aN q := by
  exact Framework.soundness tsB tsA Refinement preservation hRefinement0 hRunB

end ApprovalAuth
end Examples
end DbAppVerification
