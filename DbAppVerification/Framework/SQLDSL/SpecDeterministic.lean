import Std.Tactic.Do
import Std.Do.WP
import DbAppVerification.Framework.SQLDSL.Core

namespace DbAppVerification
namespace Framework

open Std.Do

theorem lookupParam_denotation
    (env : EvalEnv) (name : String) :
    lookupParam env name =
      (match env.params.get? name with
      | some v => .ok v
      | none => .error (.missingParam name)) := by
  rfl

theorem lookupLetRow_denotation
    (env : EvalEnv) (binding : String) (idx : Nat) :
    lookupLetRow env binding idx =
      (match env.lets.get? binding with
      | none => .error (.missingLetBinding binding)
      | some rows =>
          match rows[idx]? with
          | none => .error (.badIndex binding idx)
          | some row => .ok row) := by
  rfl

@[simp] theorem evalExpr_param_denotation
    (env : EvalEnv) (ctx : Row) (name : String) :
    evalExpr env ctx (.param name) = lookupParam env name := by
  rfl

@[simp] theorem evalExpr_letCol_denotation
    (env : EvalEnv) (ctx : Row) (binding : String) (idx : Nat) (col : String) :
    evalExpr env ctx (.letCol binding idx col) =
      (do
        let row ← lookupLetRow env binding idx
        getRowCol row col) := by
  rfl

theorem evalQueryFrom_denotation
    (db : DB) (baseTable : String) :
    evalQueryFrom db baseTable =
      (do
        let base ← sortedRows db baseTable
        pure (base.map (fun (_, row) => qualifyRow baseTable row))) := by
  rfl

theorem evalQueryJoinStep_denotation
    (db : DB) (acc : List Row) (j : JoinSpec) :
    evalQueryJoinStep db acc j =
      (do
        let rhs ← sortedRows db j.table
        let rhsRows := rhs.map (fun (_, row) => qualifyRow j.table row)
        let mut out : List Row := []
        for leftCtx in acc do
          for rightCtx in rhsRows do
            let lv ← getRowCol leftCtx j.leftRef
            let rv ← getRowCol rightCtx j.rightRef
            if lv = rv then
              out := out.concat (mergeRow leftCtx rightCtx)
        pure out) := by
  rfl

theorem evalQueryJoins_denotation
    (db : DB) (initCtxs : List Row) (joins : List JoinSpec) :
    evalQueryJoins db initCtxs joins =
      joins.foldlM (fun acc j => evalQueryJoinStep db acc j) initCtxs := by
  rfl

theorem evalQueryWhereCore_denotation
    (rows : List Row) (checkRow : Row → Except ExecErr Bool) :
    evalQueryWhereCore rows checkRow =
      rows.foldlM
        (fun acc row => do
          let ok ← checkRow row
          if ok then
            pure (acc.concat row)
          else
            pure acc)
        [] := by
  rfl

theorem evalQueryProject_denotation
    (rows : List Row) (project : List String) :
    evalQueryProject rows project =
      rows.foldlM
        (fun acc row => do
          let projected :=
            project.foldl
              (fun proj name =>
                match row.get? name with
                | some v => proj.insert name v
                | none => proj)
              ({} : Row)
          pure (acc.concat projected))
        [] := by
  rfl

theorem evalQuery_denotation_helpers
    (db : DB) (env : EvalEnv) (q : Query) :
    evalQuery db env q =
      (do
        let initCtxs ← evalQueryFrom db q.baseTable
        let joined ← evalQueryJoins db initCtxs q.joins
        let filtered ←
          match h : q.where? with
          | none => pure joined
          | some p =>
              have h : sizeOf p < sizeOf q := by
                obtain ⟨ _ ⟩ := q
                subst h
                simp
                omega
              evalQueryWhereCore joined (fun row => evalPred db env row p)
        evalQueryProject filtered q.project) := by
  unfold evalQuery
  rfl

@[simp] theorem execStmt_assert_denotation
    (schema : Schema) (pred : Pred) (msg : String) (env : EvalEnv) (db : DB) :
    execStmt schema (.assert pred msg) env db =
      (do
        let ok ← evalPred db env {} pred
        if ok then
          pure (db, env)
        else
          .error (.assertFailed msg)) := by
  rfl

@[simp] theorem execStmt_seq_denotation
    (schema : Schema) (s1 s2 : Stmt) (env : EvalEnv) (db : DB) :
    execStmt schema (.seq s1 s2) env db =
      (do
        let (db1, env1) ← execStmt schema s1 env db
        execStmt schema s2 env1 db1) := by
  rfl

@[simp] theorem execStmt_letQ_denotation
    (schema : Schema) (name : String) (q : Query) (body : Stmt) (env : EvalEnv) (db : DB) :
    execStmt schema (.letQ name q body) env db =
      (do
        let rows ← evalQuery db env q
        let env' := { env with lets := env.lets.insert name rows }
        execStmt schema body env' db) := by
  rfl

theorem execStmt_assert_eq_of_evalPred_true
    (schema : Schema) (pred : Pred) (msg : String) (env : EvalEnv) (db : DB)
    (hPred : evalPred db env {} pred = .ok true) :
    execStmt schema (.assert pred msg) env db = .ok (db, env) := by
  rw [execStmt, hPred]
  rfl

theorem execStmt_assert_eq_of_evalPred_false
    (schema : Schema) (pred : Pred) (msg : String) (env : EvalEnv) (db : DB)
    (hPred : evalPred db env {} pred = .ok false) :
    execStmt schema (.assert pred msg) env db = .error (.assertFailed msg) := by
  rw [execStmt, hPred]
  rfl

theorem execStmt_assert_eq_of_evalPred_error
    (schema : Schema) (pred : Pred) (msg : String) (env : EvalEnv) (db : DB) (e : ExecErr)
    (hPred : evalPred db env {} pred = .error e) :
    execStmt schema (.assert pred msg) env db = .error e := by
  rw [execStmt, hPred]
  rfl

theorem sortedRows_spec_trivial
    (db : DB) (table : String) :
    ⦃⌜True⌝⦄ sortedRows db table
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : sortedRows db table <;> simp [Triple, wp, Id.run]

theorem getRowCol_spec_trivial
    (row : Row) (name : String) :
    ⦃⌜True⌝⦄ getRowCol row name
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : getRowCol row name <;> simp [Triple, wp, Id.run]

theorem lookupParam_spec_trivial
    (env : EvalEnv) (name : String) :
    ⦃⌜True⌝⦄ lookupParam env name
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : lookupParam env name <;> simp [Triple, wp, Id.run]

theorem lookupLetRow_spec_trivial
    (env : EvalEnv) (binding : String) (idx : Nat) :
    ⦃⌜True⌝⦄ lookupLetRow env binding idx
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : lookupLetRow env binding idx <;> simp [Triple, wp, Id.run]

theorem evalQueryFrom_spec_trivial
    (db : DB) (baseTable : String) :
    ⦃⌜True⌝⦄ evalQueryFrom db baseTable
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : evalQueryFrom db baseTable <;> simp [Triple, wp, Id.run]

theorem evalQueryJoinStep_spec_trivial
    (db : DB) (acc : List Row) (j : JoinSpec) :
    ⦃⌜True⌝⦄ evalQueryJoinStep db acc j
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : evalQueryJoinStep db acc j <;> simp [Triple, wp, Id.run]

theorem evalQueryJoins_spec_trivial
    (db : DB) (initCtxs : List Row) (joins : List JoinSpec) :
    ⦃⌜True⌝⦄ evalQueryJoins db initCtxs joins
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : evalQueryJoins db initCtxs joins <;> simp [Triple, wp, Id.run]

theorem evalQueryWhereCore_spec_trivial
    (rows : List Row) (checkRow : Row → Except ExecErr Bool) :
    ⦃⌜True⌝⦄ evalQueryWhereCore rows checkRow
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : evalQueryWhereCore rows checkRow <;> simp [Triple, wp, Id.run]

theorem evalQueryProject_spec_trivial
    (rows : List Row) (project : List String) :
    ⦃⌜True⌝⦄ evalQueryProject rows project
      ⦃post⟨fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ := by
  cases h : evalQueryProject rows project <;> simp [Triple, wp, Id.run]

theorem except_exact_spec {ε α : Type} (x : Except ε α) :
    ⦃⌜True⌝⦄ x
      ⦃post⟨fun a => ⌜x = .ok a⌝, fun e => ⌜x = .error e⌝⟩⦄ := by
  cases h : x <;> simp [Triple, wp, Id.run]

private def projectedRows (rows : List Row) (project : List String) : List Row :=
  (rows.map (fun x2 =>
    [project.foldl
      (fun proj name =>
        match x2.get? name with
        | some v => proj.insert name v
        | none => proj)
      ({} : Row)])).flatten

theorem evalQueryFrom_ok_structure
    (db : DB) (baseTable : String) (rows : List Row)
    (hEval : evalQueryFrom db baseTable = .ok rows) :
    ∃ base,
      sortedRows db baseTable = .ok base ∧
      rows = base.map (fun (_, row) => qualifyRow baseTable row) := by
  unfold evalQueryFrom at hEval
  cases hBase : sortedRows db baseTable with
  | error e =>
      simp [hBase] at hEval
      cases hEval
  | ok base =>
      simp [hBase] at hEval
      cases hEval
      exact ⟨base, by simp [hBase], rfl⟩

theorem evalQueryFrom_error_structure
    (db : DB) (baseTable : String) (e : ExecErr)
    (hEval : evalQueryFrom db baseTable = .error e) :
    sortedRows db baseTable = .error e := by
  unfold evalQueryFrom at hEval
  cases hBase : sortedRows db baseTable with
  | error e' =>
      simp [hBase] at hEval
      cases hEval
      simp
  | ok base =>
      simp [hBase] at hEval
      cases hEval

theorem evalQueryProject_eq_ok_projectedRows
    (rows : List Row) (project : List String) :
    evalQueryProject rows project = .ok (projectedRows rows project) := by
  unfold evalQueryProject projectedRows
  simp
  change Except.ok
      ((List.map
          (fun x2 =>
            [List.foldl
                (fun proj name =>
                  match x2[name]? with
                  | some v => Std.HashMap.insert proj name v
                  | none => proj)
                ∅ project])
          rows).flatten) =
    Except.ok
      ((List.map
          (fun x2 =>
            [List.foldl
                (fun proj name =>
                  match x2[name]? with
                  | some v => Std.HashMap.insert proj name v
                  | none => proj)
                ∅ project])
          rows).flatten)
  rfl

@[spec] theorem sortedRows_spec_struct
    (db : DB) (table : String) :
    ⦃⌜True⌝⦄ sortedRows db table
      ⦃post⟨fun rows =>
              ⌜DB.selectMany db table (fun _ => true) = .ok rows⌝,
              fun e =>
              ⌜∃ dbe,
                  DB.selectMany db table (fun _ => true) = .error dbe ∧
                  e = .db dbe⌝⟩⦄ := by
  unfold sortedRows liftDB
  cases hSel : DB.selectMany db table (fun _ => true) with
  | ok rows =>
      simp [Triple, wp, Id.run, Except.mapError]
  | error dbe =>
      simp [Triple, wp, Id.run, Except.mapError]

@[spec] theorem getRowCol_spec_struct
    (row : Row) (name : String) :
    ⦃⌜True⌝⦄ getRowCol row name
      ⦃post⟨fun v => ⌜row.get? name = some v⌝,
              fun e => ⌜row.get? name = none ∧ e = .missingColumn name⌝⟩⦄ := by
  unfold getRowCol
  cases row.get? name <;> simp [Triple, wp, Id.run]

@[spec] theorem lookupParam_spec_struct
    (env : EvalEnv) (name : String) :
    ⦃⌜True⌝⦄ lookupParam env name
      ⦃post⟨fun v => ⌜env.params.get? name = some v⌝,
              fun e => ⌜env.params.get? name = none ∧ e = .missingParam name⌝⟩⦄ := by
  unfold lookupParam
  cases env.params.get? name <;> simp [Triple, wp, Id.run]

@[spec] theorem lookupLetRow_spec_struct
    (env : EvalEnv) (binding : String) (idx : Nat) :
    ⦃⌜True⌝⦄ lookupLetRow env binding idx
      ⦃post⟨fun r =>
              ⌜∃ rows,
                  env.lets.get? binding = some rows ∧
                  rows[idx]? = some r⌝,
              fun e =>
              ⌜(env.lets.get? binding = none ∧ e = .missingLetBinding binding) ∨
                (∃ rows,
                    env.lets.get? binding = some rows ∧
                    e = .badIndex binding idx)⌝⟩⦄ := by
  unfold lookupLetRow
  cases hLet : env.lets.get? binding with
  | none =>
      simp [Triple, wp, Id.run]
  | some rows =>
      cases hIdx : rows[idx]? with
      | none =>
          simp [Triple, wp, Id.run, hIdx]
      | some row =>
          simp [Triple, wp, Id.run, hIdx]

@[spec] theorem evalQueryFrom_spec_struct
    (db : DB) (baseTable : String) :
    ⦃⌜True⌝⦄ evalQueryFrom db baseTable
      ⦃post⟨fun rows =>
              ⌜∃ base,
                  sortedRows db baseTable = .ok base ∧
                  rows = base.map (fun (_, row) => qualifyRow baseTable row)⌝,
              fun e => ⌜sortedRows db baseTable = .error e⌝⟩⦄ := by
  cases hEval : evalQueryFrom db baseTable with
  | ok rows =>
      simp [Triple, wp, Id.run]
      exact evalQueryFrom_ok_structure db baseTable rows hEval
  | error e =>
      simp [Triple, wp, Id.run]
      exact evalQueryFrom_error_structure db baseTable e hEval

@[spec] theorem evalQueryProject_spec_total
    (rows : List Row) (project : List String) :
    ⦃⌜True⌝⦄ evalQueryProject rows project
      ⦃post⟨fun out => ⌜out = projectedRows rows project⌝,
              fun _ => ⌜False⌝⟩⦄ := by
  rw [evalQueryProject_eq_ok_projectedRows]
  simp [Triple, wp, Id.run]

theorem sortedRows_spec_exact
    (db : DB) (table : String) :
    ⦃⌜True⌝⦄ sortedRows db table
      ⦃post⟨fun rows => ⌜sortedRows db table = .ok rows⌝,
              fun e => ⌜sortedRows db table = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := sortedRows db table)

theorem getRowCol_spec_exact
    (row : Row) (name : String) :
    ⦃⌜True⌝⦄ getRowCol row name
      ⦃post⟨fun v => ⌜getRowCol row name = .ok v⌝,
              fun e => ⌜getRowCol row name = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := getRowCol row name)

theorem lookupParam_spec_exact
    (env : EvalEnv) (name : String) :
    ⦃⌜True⌝⦄ lookupParam env name
      ⦃post⟨fun v => ⌜lookupParam env name = .ok v⌝,
              fun e => ⌜lookupParam env name = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := lookupParam env name)

theorem lookupLetRow_spec_exact
    (env : EvalEnv) (binding : String) (idx : Nat) :
    ⦃⌜True⌝⦄ lookupLetRow env binding idx
      ⦃post⟨fun r => ⌜lookupLetRow env binding idx = .ok r⌝,
              fun e => ⌜lookupLetRow env binding idx = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := lookupLetRow env binding idx)

theorem evalQueryFrom_spec_exact
    (db : DB) (baseTable : String) :
    ⦃⌜True⌝⦄ evalQueryFrom db baseTable
      ⦃post⟨fun rows => ⌜evalQueryFrom db baseTable = .ok rows⌝,
              fun e => ⌜evalQueryFrom db baseTable = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := evalQueryFrom db baseTable)

@[spec] theorem evalQueryJoinStep_spec_exact
    (db : DB) (acc : List Row) (j : JoinSpec) :
    ⦃⌜True⌝⦄ evalQueryJoinStep db acc j
      ⦃post⟨fun rows => ⌜evalQueryJoinStep db acc j = .ok rows⌝,
              fun e => ⌜evalQueryJoinStep db acc j = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := evalQueryJoinStep db acc j)

@[spec] theorem evalQueryJoins_spec_exact
    (db : DB) (initCtxs : List Row) (joins : List JoinSpec) :
    ⦃⌜True⌝⦄ evalQueryJoins db initCtxs joins
      ⦃post⟨fun rows => ⌜evalQueryJoins db initCtxs joins = .ok rows⌝,
              fun e => ⌜evalQueryJoins db initCtxs joins = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := evalQueryJoins db initCtxs joins)

@[spec] theorem evalQueryWhereCore_spec_exact
    (rows : List Row) (checkRow : Row → Except ExecErr Bool) :
    ⦃⌜True⌝⦄ evalQueryWhereCore rows checkRow
      ⦃post⟨fun out => ⌜evalQueryWhereCore rows checkRow = .ok out⌝,
              fun e => ⌜evalQueryWhereCore rows checkRow = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := evalQueryWhereCore rows checkRow)

theorem evalQueryProject_spec_exact
    (rows : List Row) (project : List String) :
    ⦃⌜True⌝⦄ evalQueryProject rows project
      ⦃post⟨fun out => ⌜evalQueryProject rows project = .ok out⌝,
              fun e => ⌜evalQueryProject rows project = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := evalQueryProject rows project)

@[spec] theorem evalQuery_spec_exact
    (db : DB) (env : EvalEnv) (q : Query) :
    ⦃⌜True⌝⦄ evalQuery db env q
      ⦃post⟨fun rows => ⌜evalQuery db env q = .ok rows⌝,
              fun e => ⌜evalQuery db env q = .error e⌝⟩⦄ := by
  simpa using except_exact_spec (x := evalQuery db env q)

  @[simp] theorem evalQuery_noJoin_noWhere_denotation
    (db : DB) (env : EvalEnv) (baseTable : String) (project : List String) :
    evalQuery db env ({ baseTable := baseTable, joins := [], where? := none, project := project } : Query) =
      (do
        let base ← sortedRows db baseTable
        let initCtxs : List Row := base.map (fun (_, row) => qualifyRow baseTable row)
        let joined ← pure initCtxs
        let filtered ← pure joined
        filtered.foldlM
          (fun acc row => do
            let projected :=
              project.foldl
                (fun proj name =>
                  match row.get? name with
                  | some v => proj.insert name v
                  | none => proj)
                ({} : Row)
            pure (acc.concat projected))
          []) := by
  simpa [evalQuery, evalQueryFrom_denotation, evalQueryJoins_denotation,
    evalQueryProject_denotation, List.foldlM_nil]

  @[simp] theorem evalQuery_noJoin_withWhere_denotation
    (db : DB) (env : EvalEnv) (baseTable : String) (pred : Pred) (project : List String) :
    evalQuery db env ({ baseTable := baseTable, joins := [], where? := some pred, project := project } : Query) =
      (do
        let base ← sortedRows db baseTable
        let initCtxs : List Row := base.map (fun (_, row) => qualifyRow baseTable row)
        let joined ← pure initCtxs
        let filtered ←
          joined.foldlM
            (fun acc row => do
              let ok ← evalPred db env row pred
              if ok then
                pure (acc.concat row)
              else
                pure acc)
            []
        filtered.foldlM
          (fun acc row => do
            let projected :=
              project.foldl
                (fun proj name =>
                  match row.get? name with
                  | some v => proj.insert name v
                  | none => proj)
                ({} : Row)
            pure (acc.concat projected))
          []) := by
  simpa [evalQuery, evalQueryFrom_denotation, evalQueryJoins_denotation,
    evalQueryWhereCore_denotation, evalQueryProject_denotation, List.foldlM_nil]

@[spec] theorem execStmt_assert_true_lit_spec
    (schema : Schema) (env : EvalEnv) (db : DB) (msg : String) :
    ⦃⌜True⌝⦄ execStmt schema (.assert (.eq (.lit (.bool true)) (.lit (.bool true))) msg) env db
      ⦃post⟨fun x => ⌜x = (db, env)⌝, fun _ => ⌜False⌝⟩⦄ := by
  mvcgen [execStmt, evalPred, evalExpr]
  all_goals mleave
  all_goals simp

@[spec] theorem execStmt_assert_false_lit_spec
    (schema : Schema) (env : EvalEnv) (db : DB) (msg : String) :
    ⦃⌜True⌝⦄ execStmt schema (.assert (.eq (.lit (.bool true)) (.lit (.bool false))) msg) env db
      ⦃post⟨fun _ => ⌜False⌝, fun e => ⌜e = .assertFailed msg⌝⟩⦄ := by
  mvcgen [execStmt, evalPred, evalExpr]
  all_goals mleave
  all_goals simp

end Framework
end DbAppVerification
