import Std

namespace DbAppVerification
namespace Framework

universe uCmd uErr uQ uR uState uSA uSB

structure TransitionSystem
    (Cmd : Type uCmd) (Err : Type uErr) (Q : Type uQ) (R : Type uR) where
  State : Type uState
  step : State → Cmd → Except Err State
  query : State → Q → R

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
    (Ref : tsImpl.State → tsAbs.State → Prop) : Prop where
  step_success :
    ∀ {b a c a'},
      Ref b a →
      tsAbs.step a c = .ok a' →
      ∃ b', tsImpl.step b c = .ok b' ∧ Ref b' a'
  step_error_align :
    ∀ {b a c eB},
      Ref b a →
      tsImpl.step b c = .error eB →
      ∃ eA, tsAbs.step a c = .error eA ∧ eA = eB
  query_preserve :
    ∀ {b a q}, Ref b a → tsImpl.query b q = tsAbs.query a q

/-- Main forward-simulation soundness over finite traces. -/
theorem soundness
    {Cmd : Type uCmd} {Err : Type uErr} {Q : Type uQ} {R : Type uR}
    (tsImpl tsAbs : TransitionSystem Cmd Err Q R)
    (Ref : tsImpl.State → tsAbs.State → Prop)
    (hPres : Preservation tsImpl tsAbs Ref)
    {b0 : tsImpl.State} {a0 : tsAbs.State} {cmds : List Cmd}
    {bN : tsImpl.State} {aN : tsAbs.State}
    (hRef0 : Ref b0 a0)
    (hRunImpl : tsImpl.run b0 cmds = .ok bN)
    (hRunAbs : tsAbs.run a0 cmds = .ok aN) :
    Ref bN aN ∧ ∀ q, tsImpl.query bN q = tsAbs.query aN q := by
  induction cmds generalizing b0 a0 bN aN with
  | nil =>
      simp [TransitionSystem.run] at hRunImpl hRunAbs
      subst hRunImpl
      subst hRunAbs
      exact ⟨hRef0, fun q => hPres.query_preserve hRef0⟩
  | cons c cs ih =>
      cases hAstep : tsAbs.step a0 c with
      | error e =>
          simp [TransitionSystem.run, hAstep] at hRunAbs
      | ok a1 =>
          simp [TransitionSystem.run, hAstep] at hRunAbs
          cases hBstep : tsImpl.step b0 c with
          | error e =>
              simp [TransitionSystem.run, hBstep] at hRunImpl
          | ok b1run =>
              simp [TransitionSystem.run, hBstep] at hRunImpl
              have hStep := hPres.step_success hRef0 hAstep
              rcases hStep with ⟨b1, hBok, hRef1⟩
              have hb1eq : b1 = b1run := by
                rw [hBstep] at hBok
                cases hBok
                rfl
              subst hb1eq
              have hTail := ih hRef1 hRunImpl hRunAbs
              rcases hTail with ⟨hRefN, hQueryN⟩
              exact ⟨hRefN, hQueryN⟩

end Framework
end DbAppVerification
