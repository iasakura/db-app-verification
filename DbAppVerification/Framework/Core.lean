import Std

namespace DbAppVerification
namespace Framework

universe uCmd uErr uQ uR uState uSA uSB

class InvariantState (σ : Type uState) where
  inv : σ → Prop

def stateInv {σ : Type uState} [InvariantState σ] (s : σ) : Prop :=
  InvariantState.inv s

structure TransitionSystem
    (Cmd : Type uCmd) (Err : Type uErr) (Q : Type uQ) (R : Type uR) where
  State : Type uState
  step : State → Cmd → Except Err State
  query : State → Q → R
  stateInvariant : InvariantState State := by infer_instance

attribute [instance] TransitionSystem.stateInvariant

/-- Refinement induced by an abstraction function. -/
def RefOfAbs {SB : Type uSB} {SA : Type uSA} (abs : SB → SA) : SB → SA → Prop :=
  fun b a => abs b = a

def TransitionSystem.run
    {Cmd : Type uCmd} {Err : Type uErr} {Q : Type uQ} {R : Type uR}
    (ts : TransitionSystem Cmd Err Q R) :
    ts.State → List Cmd → Except Err ts.State
  | s, [] => .ok s
  | s, c :: cs =>
      match ts.step s c with
      | .ok s' => ts.run s' cs
      | .error e => .error e

structure Preservation
    {Cmd : Type uCmd} {Err : Type uErr} {Q : Type uQ} {R : Type uR}
    (tsImpl tsAbs : TransitionSystem Cmd Err Q R)
    (Refinement : tsImpl.State → tsAbs.State → Prop)
    [InvariantState tsImpl.State] [InvariantState tsAbs.State] : Prop where
  refinement_inv_impl :
    ∀ {b a}, Refinement b a → stateInv b
  refinement_inv_abs :
    ∀ {b a}, Refinement b a → stateInv a
  step_success :
    ∀ {b a c b'},
      Refinement b a →
      tsImpl.step b c = .ok b' →
      ∃ a', tsAbs.step a c = .ok a' ∧ Refinement b' a'
  step_error_align :
    ∀ {b a c eB},
      Refinement b a →
      tsImpl.step b c = .error eB →
      ∃ eA, tsAbs.step a c = .error eA ∧ eA = eB
  query_preserve :
    ∀ {b a q}, Refinement b a → tsImpl.query b q = tsAbs.query a q

/-- Main forward-simulation soundness over finite traces. -/
theorem soundness
    {Cmd : Type uCmd} {Err : Type uErr} {Q : Type uQ} {R : Type uR}
    (tsImpl tsAbs : TransitionSystem Cmd Err Q R)
    (Refinement : tsImpl.State → tsAbs.State → Prop)
    [InvariantState tsImpl.State] [InvariantState tsAbs.State]
    (hPres : Preservation tsImpl tsAbs Refinement)
    {b0 : tsImpl.State} {a0 : tsAbs.State} {cmds : List Cmd} {bN : tsImpl.State}
    (hRefinement0 : Refinement b0 a0)
    (hRunImpl : tsImpl.run b0 cmds = .ok bN) :
    ∃ aN, tsAbs.run a0 cmds = .ok aN ∧ Refinement bN aN ∧
      ∀ q, tsImpl.query bN q = tsAbs.query aN q := by
  induction cmds generalizing b0 a0 bN with
  | nil =>
      simp [TransitionSystem.run] at hRunImpl
      subst hRunImpl
      refine ⟨a0, by simp [TransitionSystem.run], hRefinement0, ?_⟩
      intro q
      exact hPres.query_preserve hRefinement0
  | cons c cs ih =>
      cases hBstep : tsImpl.step b0 c with
      | error e =>
          simp [TransitionSystem.run, hBstep] at hRunImpl
      | ok b1 =>
          simp [TransitionSystem.run, hBstep] at hRunImpl
          have hStep := hPres.step_success hRefinement0 hBstep
          rcases hStep with ⟨a1, hAstep, hRef1⟩
          have hTail := ih hRef1 hRunImpl
          rcases hTail with ⟨aN, hRunAbsTail, hRefN, hQueryN⟩
          refine ⟨aN, ?_, hRefN, hQueryN⟩
          simp [TransitionSystem.run, hAstep, hRunAbsTail]

end Framework
end DbAppVerification
