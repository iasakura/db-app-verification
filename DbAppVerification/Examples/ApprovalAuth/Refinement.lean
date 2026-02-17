import Std
import DbAppVerification.Framework.Core
import DbAppVerification.Framework.DB
import DbAppVerification.Examples.ApprovalAuth.SpecA
import DbAppVerification.Examples.ApprovalAuth.ImplB

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
    employed := absEmployed db
    manager := absManagers db
    docExists := absDocuments db
    histContent := absHistories db
    proposals := absProposals db
    decision := absDecisions db
  }

abbrev Ref : SB → SA → Prop := RefOfAbs abs

/-- TODO: mechanize each constructor case directly against DSL semantics. -/
axiom stepPreservation : StepPreservation Ref stepA stepB

/-- TODO: discharge by unfolding accepted-doc query and proving row/map correspondence. -/
axiom queryPreservation : QueryPreservation Ref queryA queryB

theorem approval_refinement_sound
    {b0 : SB} {a0 : SA} {cmds : List Cmd} {bN : SB} {aN : SA}
    (hRef0 : Ref b0 a0)
    (hRunA : Framework.runA stepA a0 cmds = .ok aN)
    (hRunB : Framework.runB stepB b0 cmds = .ok bN) :
    Ref bN aN ∧ ∀ q, queryB bN q = queryA aN q := by
  exact Framework.soundness Ref stepA stepB queryA queryB stepPreservation queryPreservation hRef0 hRunA hRunB

end ApprovalAuth
end Examples
end DbAppVerification
