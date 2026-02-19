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

abbrev Refinement : SB → SA → Prop := RefOfAbs abs

/-- TODO: mechanize command and query preservation against DSL semantics. -/
theorem preservation : Preservation tsB tsA Refinement := by
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
