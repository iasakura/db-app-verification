import Mathlib
import DbAppVerification.Framework.Core

namespace DbAppVerification
namespace Examples
namespace ApprovalAuth

abbrev EmployeeId := Nat
abbrev DocumentId := Nat
abbrev HistoryId := Nat
abbrev ProposalId := Nat
abbrev Doc := String

inductive DecisionKind where
  | accept
  | reject (comment : String)
  deriving Repr, DecidableEq

inductive Err where
  | notEmployed
  | notManager
  | missingDoc
  | missingHistory
  | missingProposal
  | alreadyDecided
  | unauthorized
  | constraintViolation
  deriving Repr, DecidableEq

structure SA where
  employed : Finset EmployeeId
  manager : Finset (EmployeeId × EmployeeId)
  docExists : Finset DocumentId
  histContent : Finset (DocumentId × HistoryId × Doc)
  proposals : Finset (ProposalId × EmployeeId × EmployeeId × DocumentId × HistoryId)
  decision : Finset (ProposalId × EmployeeId × DecisionKind)

instance : DbAppVerification.Framework.InvariantState SA where
  inv := fun _ => True

inductive Cmd where
  | Employ (e : EmployeeId)
  | AddManager (m : EmployeeId) (e : EmployeeId)
  | NewDocument (did : DocumentId)
  | AddHistory (did : DocumentId) (hid : HistoryId) (doc : Doc)
  | Propose (sender : EmployeeId) (target : EmployeeId) (did : DocumentId) (hid : HistoryId) (pid : ProposalId)
  | Accept (actor : EmployeeId) (pid : ProposalId)
  | Reject (actor : EmployeeId) (pid : ProposalId) (comment : String)
  deriving Repr, DecidableEq

inductive Q where
  | AcceptedProposalFrom (sender : EmployeeId) (pid : ProposalId)
  deriving Repr, DecidableEq

abbrev R := Option Doc

def emptySA : SA :=
  {
    employed := {}
    manager := {}
    docExists := {}
    histContent := {}
    proposals := {}
    decision := {}
  }

private noncomputable def hasHistory (s : SA) (did : DocumentId) (hid : HistoryId) : Bool :=
  s.histContent.toList.any fun
    | (did', hid', _) => did' == did && hid' == hid

private noncomputable def historyDocOf? (s : SA) (did : DocumentId) (hid : HistoryId) : Option Doc :=
  (s.histContent.toList.find? fun
      | (did', hid', _) => did' == did && hid' == hid).map fun
    | (_, _, doc) => doc

private noncomputable def proposalOf? (s : SA) (pid : ProposalId) :
    Option (ProposalId × EmployeeId × EmployeeId × DocumentId × HistoryId) :=
  s.proposals.toList.find? fun
    | (pid', _, _, _, _) => pid' == pid

private noncomputable def hasDecision (s : SA) (pid : ProposalId) : Bool :=
  s.decision.toList.any fun
    | (pid', _, _) => pid' == pid

private noncomputable def decisionOf? (s : SA) (pid : ProposalId) :
    Option (ProposalId × EmployeeId × DecisionKind) :=
  s.decision.toList.find? fun
    | (pid', _, _) => pid' == pid

noncomputable def stepA (s : SA) : Cmd → Except Err SA
  | .Employ e =>
      if e ∈ s.employed then
        .error .constraintViolation
      else
        .ok { s with employed := insert e s.employed }
  | .AddManager m e =>
      if (m, e) ∈ s.manager then
        .error .constraintViolation
      else
        .ok { s with manager := insert (m, e) s.manager }
  | .NewDocument did =>
      if did ∈ s.docExists then
        .error .constraintViolation
      else
        .ok { s with docExists := insert did s.docExists }
  | .AddHistory did hid doc =>
      if did ∈ s.docExists then
        if hasHistory s did hid then
          .error .constraintViolation
        else
          .ok { s with histContent := insert (did, hid, doc) s.histContent }
      else
        .error .missingDoc
  | .Propose sender target did hid pid =>
      if sender ∉ s.employed || target ∉ s.employed then
        .error .notEmployed
      else if (target, sender) ∉ s.manager then
        .error .notManager
      else if did ∉ s.docExists then
        .error .missingDoc
      else if !(hasHistory s did hid) then
        .error .missingHistory
      else if (proposalOf? s pid).isSome then
        .error .constraintViolation
      else
        .ok {
          s with
          proposals := insert (pid, sender, target, did, hid) s.proposals
        }
  | .Accept actor pid =>
      match proposalOf? s pid with
      | none => .error .missingProposal
      | some (_pid, _sender, target, _did, _hid) =>
          if actor ≠ target then
            .error .unauthorized
          else if hasDecision s pid then
            .error .alreadyDecided
          else
            .ok { s with decision := insert (pid, actor, .accept) s.decision }
  | .Reject actor pid comment =>
      match proposalOf? s pid with
      | none => .error .missingProposal
      | some (_pid, _sender, target, _did, _hid) =>
          if actor ≠ target then
            .error .unauthorized
          else if hasDecision s pid then
            .error .alreadyDecided
          else
            .ok { s with decision := insert (pid, actor, .reject comment) s.decision }

noncomputable def queryA (s : SA) : Q → R
  | .AcceptedProposalFrom sender pid =>
      match proposalOf? s pid, decisionOf? s pid with
      | some (_pid, sender', _target, did, hid), some (_pid', _by, .accept) =>
          if sender' = sender then historyDocOf? s did hid else none
      | _, _ =>
          none

noncomputable def tsA : Framework.TransitionSystem Cmd Err Q R where
  State := SA
  step := stepA
  query := queryA

end ApprovalAuth
end Examples
end DbAppVerification
