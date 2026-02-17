import Std

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
  employed : Std.HashSet EmployeeId
  manager : Std.HashSet (EmployeeId × EmployeeId)
  docExists : Std.HashSet DocumentId
  histContent : Std.HashMap (DocumentId × HistoryId) Doc
  proposals : Std.HashMap ProposalId (EmployeeId × EmployeeId × DocumentId × HistoryId)
  decision : Std.HashMap ProposalId (EmployeeId × DecisionKind)
  deriving Repr

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

private def hasHistory (s : SA) (did : DocumentId) (hid : HistoryId) : Bool :=
  (s.histContent.get? (did, hid)).isSome

def stepA (s : SA) : Cmd → Except Err SA
  | .Employ e =>
      .ok { s with employed := s.employed.insert e }
  | .AddManager m e =>
      .ok { s with manager := s.manager.insert (m, e) }
  | .NewDocument did =>
      .ok { s with docExists := s.docExists.insert did }
  | .AddHistory did hid doc =>
      if s.docExists.contains did then
        .ok { s with histContent := s.histContent.insert (did, hid) doc }
      else
        .error .missingDoc
  | .Propose sender target did hid pid =>
      if !s.employed.contains sender || !s.employed.contains target then
        .error .notEmployed
      else if !s.manager.contains (target, sender) then
        .error .notManager
      else if !s.docExists.contains did then
        .error .missingDoc
      else if !(hasHistory s did hid) then
        .error .missingHistory
      else if (s.proposals.get? pid).isSome then
        .error .constraintViolation
      else
        .ok {
          s with
          proposals := s.proposals.insert pid (sender, target, did, hid)
        }
  | .Accept actor pid =>
      match s.proposals.get? pid with
      | none => .error .missingProposal
      | some (_sender, target, _did, _hid) =>
          if (s.decision.get? pid).isSome then
            .error .alreadyDecided
          else if actor = target then
            .ok { s with decision := s.decision.insert pid (actor, .accept) }
          else
            .error .unauthorized
  | .Reject actor pid comment =>
      match s.proposals.get? pid with
      | none => .error .missingProposal
      | some (_sender, target, _did, _hid) =>
          if (s.decision.get? pid).isSome then
            .error .alreadyDecided
          else if actor = target then
            .ok { s with decision := s.decision.insert pid (actor, .reject comment) }
          else
            .error .unauthorized

def queryA (s : SA) : Q → R
  | .AcceptedProposalFrom sender pid =>
      match s.proposals.get? pid, s.decision.get? pid with
      | some (sender', _target, did, hid), some (_by, .accept) =>
          if sender' = sender then s.histContent.get? (did, hid) else none
      | _, _ =>
          none

end ApprovalAuth
end Examples
end DbAppVerification
