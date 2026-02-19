import Std
import DbAppVerification.Framework.DB
import DbAppVerification.Framework.ExportIO
import DbAppVerification.Framework.SQLDSL
import DbAppVerification.Examples.ApprovalAuth.Spec

namespace DbAppVerification
namespace Examples
namespace ApprovalAuth

open Framework

private def natV (n : Nat) : Value := .int (Int.ofNat n)

def approvalSchema : Schema :=
  {
    tables :=
      [
        {
          name := "employees"
          pkCol := "eid"
          columns :=
            [
              { name := "eid", ty := .int, nullable := false }
            ]
        },
        {
          name := "managers"
          pkCol := "mid"
          pkCols := ["mid", "eid"]
          columns :=
            [
              { name := "mid", ty := .int, nullable := false },
              { name := "eid", ty := .int, nullable := false }
            ]
        },
        {
          name := "documents"
          pkCol := "did"
          columns :=
            [
              { name := "did", ty := .int, nullable := false }
            ]
        },
        {
          name := "histories"
          pkCol := "did"
          pkCols := ["did", "hid"]
          columns :=
            [
              { name := "did", ty := .int, nullable := false },
              { name := "hid", ty := .int, nullable := false },
              { name := "doc", ty := .string, nullable := false }
            ]
        },
        {
          name := "proposals"
          pkCol := "pid"
          columns :=
            [
              { name := "pid", ty := .int, nullable := false },
              { name := "from", ty := .int, nullable := false },
              { name := "to", ty := .int, nullable := false },
              { name := "did", ty := .int, nullable := false },
              { name := "hid", ty := .int, nullable := false }
            ]
        },
        {
          name := "decisions"
          pkCol := "pid"
          columns :=
            [
              { name := "pid", ty := .int, nullable := false },
              { name := "by", ty := .int, nullable := false },
              { name := "kind", ty := .string, nullable := false },
              { name := "comment", ty := .string, nullable := true }
            ],
          fks :=
            [
              { col := "pid", refTable := "proposals", refCol := "pid" }
            ]
        }
      ]
  }

abbrev SB := DBState approvalSchema

private def existsBy (table : String) (pred : Pred) : Pred :=
  .exists { baseTable := table, where? := some pred, project := [] }

private def assertMsg (p : Pred) (msg : String) : Stmt :=
  .assert p msg

def employStmt : Stmt :=
  .insert "employees" (.param "eid") [
    ("eid", .param "eid")
  ]

private def addManagerStmt : Stmt :=
  .insert "managers" (.param "mid")
    [
      ("mid", .param "mid"),
      ("eid", .param "eid")
    ]

private def newDocumentStmt : Stmt :=
  .insert "documents" (.param "did") [
    ("did", .param "did")
  ]

private def addHistoryStmt : Stmt :=
  dsl{
    assertMsg
      (existsBy "documents" (.col "did" === .param "did"))
      "missingDoc";
    .insert "histories" (.param "did")
      [
        ("did", .param "did"),
        ("hid", .param "hid"),
        ("doc", .param "doc")
      ]
  }

private def proposeStmt : Stmt :=
  dsl{
    assertMsg (existsBy "employees" (.col "eid" === .param "from")) "notEmployed";
    assertMsg (existsBy "employees" (.col "eid" === .param "to")) "notEmployed";
    assertMsg
      (existsBy "managers"
        ((.col "mid" === .param "to") &&&
         (.col "eid" === .param "from")))
      "notManager";
    assertMsg
      (existsBy "documents" (.col "did" === .param "did"))
      "missingDoc";
    assertMsg
      (existsBy "histories"
        ((.col "did" === .param "did") &&&
         (.col "hid" === .param "hid")))
      "missingHistory";
    .insert "proposals" (.param "pid")
      [
        ("pid", .param "pid"),
        ("from", .param "from"),
        ("to", .param "to"),
        ("did", .param "did"),
        ("hid", .param "hid")
      ]
  }

private def acceptStmt : Stmt :=
  dsl{
    assertMsg
      (existsBy "proposals" (.col "pid" === .param "pid"))
      "missingProposal";
    assertMsg
      (existsBy "proposals"
        ((.col "pid" === .param "pid") &&&
         (.col "to" === .param "by")))
      "unauthorized";
    assertMsg
      (.not (existsBy "decisions" (.col "pid" === .param "pid")))
      "alreadyDecided";
    .insert "decisions" (.param "pid")
      [
        ("pid", .param "pid"),
        ("by", .param "by"),
        ("kind", .lit (.str "accept")),
        ("comment", .lit (.str ""))
      ]
  }

private def rejectStmt : Stmt :=
  dsl{
    assertMsg
      (existsBy "proposals" (.col "pid" === .param "pid"))
      "missingProposal";
    assertMsg
      (existsBy "proposals"
        ((.col "pid" === .param "pid") &&&
         (.col "to" === .param "by")))
      "unauthorized";
    assertMsg
      (.not (existsBy "decisions" (.col "pid" === .param "pid")))
      "alreadyDecided";
    .insert "decisions" (.param "pid")
      [
        ("pid", .param "pid"),
        ("by", .param "by"),
        ("kind", .lit (.str "reject")),
        ("comment", .param "comment")
      ]
  }

def handlers : Handler :=
  ({} : Handler)
    |>.insert "Employ" employStmt
    |>.insert "AddManager" addManagerStmt
    |>.insert "NewDocument" newDocumentStmt
    |>.insert "AddHistory" addHistoryStmt
    |>.insert "Propose" proposeStmt
    |>.insert "Accept" acceptStmt
    |>.insert "Reject" rejectStmt

def cmdTag : Cmd → String
  | .Employ _ => "Employ"
  | .AddManager _ _ => "AddManager"
  | .NewDocument _ => "NewDocument"
  | .AddHistory _ _ _ => "AddHistory"
  | .Propose _ _ _ _ _ => "Propose"
  | .Accept _ _ => "Accept"
  | .Reject _ _ _ => "Reject"

def cmdParams : Cmd → ParamEnv
  | .Employ e =>
      ({} : ParamEnv)
        |>.insert "eid" (natV e)
  | .AddManager m e =>
      ({} : ParamEnv)
        |>.insert "mid" (natV m)
        |>.insert "eid" (natV e)
  | .NewDocument did =>
      ({} : ParamEnv)
        |>.insert "did" (natV did)
  | .AddHistory did hid doc =>
      ({} : ParamEnv)
        |>.insert "did" (natV did)
        |>.insert "hid" (natV hid)
        |>.insert "doc" (.str doc)
  | .Propose sender target did hid pid =>
      ({} : ParamEnv)
        |>.insert "from" (natV sender)
        |>.insert "to" (natV target)
        |>.insert "did" (natV did)
        |>.insert "hid" (natV hid)
        |>.insert "pid" (natV pid)
  | .Accept actor pid =>
      ({} : ParamEnv)
        |>.insert "by" (natV actor)
        |>.insert "pid" (natV pid)
  | .Reject actor pid comment =>
      ({} : ParamEnv)
        |>.insert "by" (natV actor)
        |>.insert "pid" (natV pid)
        |>.insert "comment" (.str comment)

def mapExecErr : ExecErr → Err
  | .assertFailed "notEmployed" => .notEmployed
  | .assertFailed "notManager" => .notManager
  | .assertFailed "missingDoc" => .missingDoc
  | .assertFailed "missingHistory" => .missingHistory
  | .assertFailed "missingProposal" => .missingProposal
  | .assertFailed "alreadyDecided" => .alreadyDecided
  | .assertFailed "unauthorized" => .unauthorized
  | .db (.missingKey _ _) => .missingProposal
  | .db (.missingTable _) => .constraintViolation
  | .db (.duplicateKey _ _) => .constraintViolation
  | .db (.missingColumn _) => .constraintViolation
  | .db (.typeMismatch _) => .constraintViolation
  | .db (.constraintViolation _) => .constraintViolation
  | .unknownHandler _ => .constraintViolation
  | .missingParam _ => .constraintViolation
  | .missingColumn _ => .constraintViolation
  | .missingLetBinding _ => .constraintViolation
  | .badIndex _ _ => .constraintViolation
  | .invalidProgram _ => .constraintViolation
  | .assertFailed _ => .constraintViolation

def stepB (b : SB) (cmd : Cmd) : Except Err SB :=
  match execHandlerSafe approvalSchema handlers (cmdTag cmd) (cmdParams cmd) b with
  | .ok b' => .ok b'
  | .error e => .error (mapExecErr e)

def acceptedDocQuery : Query :=
  from "proposals"
    using
      [
        join "decisions" on "proposals.pid" == "decisions.pid",
        join "histories" on "proposals.did" == "histories.did"
      ]
    where
      (((.col "proposals.pid" === .param "pid") &&&
        (.col "proposals.from" === .param "from")) &&&
       ((.col "decisions.kind" === .lit (.str "accept")) &&&
        (.col "proposals.hid" === .col "histories.hid")))
    select ["histories.doc"]

def queryB (b : SB) : Q → R
  | .AcceptedProposalFrom sender pid =>
      let env : EvalEnv :=
        {
          params :=
            ({} : ParamEnv)
              |>.insert "from" (natV sender)
              |>.insert "pid" (natV pid)
        }
      match evalQuery b.db env acceptedDocQuery with
      | .ok rows =>
          match rows[0]? with
          | some row =>
              match row.get? "histories.doc" with
              | some (.str s) => some s
              | _ => none
          | none => none
      | .error _ => none

def tsB : Framework.TransitionSystem Cmd Err Q R where
  State := SB
  step := stepB
  query := queryB

def emitDDLString : String :=
  emitDDL approvalSchema

def handlerOrder : List String :=
  ["Employ", "AddManager", "NewDocument", "AddHistory", "Propose", "Accept", "Reject"]

def emitHandlerSQLStrings : List (String × String) :=
  handlerOrder.map fun tag =>
    match emitHandlerSQL handlers tag with
    | .ok sql => (tag, sql)
    | .error _ => (tag, "-- missing handler")

def emitHTTPStubsString : String :=
  emitHTTPStubs handlers

def approvalArtifacts : ExportArtifacts :=
  {
    ddl := emitDDLString
    handlers := emitHandlerSQLStrings
    httpStubs := emitHTTPStubsString
  }

end ApprovalAuth
end Examples
end DbAppVerification
