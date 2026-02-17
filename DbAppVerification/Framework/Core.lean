import Std

namespace DbAppVerification
namespace Framework

universe uCmd uErr uResp uSA uSB uQ uR

abbrev StepA (SA : Type uSA) (Cmd : Type uCmd) (Err : Type uErr) :=
  SA → Cmd → Except Err SA

abbrev StepB (SB : Type uSB) (Cmd : Type uCmd) (Err : Type uErr) :=
  SB → Cmd → Except Err SB

abbrev QueryA (SA : Type uSA) (Q : Type uQ) (R : Type uR) := SA → Q → R
abbrev QueryB (SB : Type uSB) (Q : Type uQ) (R : Type uR) := SB → Q → R

/-- Refinement induced by an abstraction function. -/
def RefOfAbs {SB : Type uSB} {SA : Type uSA} (abs : SB → SA) : SB → SA → Prop :=
  fun b a => abs b = a

structure StepPreservation
    {SA : Type uSA} {SB : Type uSB} {Cmd : Type uCmd} {Err : Type uErr}
    (Ref : SB → SA → Prop)
    (stepA : StepA SA Cmd Err)
    (stepB : StepB SB Cmd Err) : Prop where
  success :
    ∀ {b a c a'},
      Ref b a →
      stepA a c = .ok a' →
      ∃ b', stepB b c = .ok b' ∧ Ref b' a'
  errorAlign :
    ∀ {b a c eB},
      Ref b a →
      stepB b c = .error eB →
      ∃ eA, stepA a c = .error eA ∧ eA = eB

structure QueryPreservation
    {SA : Type uSA} {SB : Type uSB} {Q : Type uQ} {R : Type uR}
    (Ref : SB → SA → Prop)
    (queryA : QueryA SA Q R)
    (queryB : QueryB SB Q R) : Prop where
  preserve : ∀ {b a q}, Ref b a → queryB b q = queryA a q

def runA {SA : Type uSA} {Cmd : Type uCmd} {Err : Type uErr}
    (stepA : StepA SA Cmd Err) : SA → List Cmd → Except Err SA
  | s, [] => .ok s
  | s, c :: cs =>
      match stepA s c with
      | .ok s' => runA stepA s' cs
      | .error e => .error e

def runB {SB : Type uSB} {Cmd : Type uCmd} {Err : Type uErr}
    (stepB : StepB SB Cmd Err) : SB → List Cmd → Except Err SB
  | s, [] => .ok s
  | s, c :: cs =>
      match stepB s c with
      | .ok s' => runB stepB s' cs
      | .error e => .error e

/-- Main forward-simulation soundness over finite traces. -/
theorem soundness
    {SA : Type uSA} {SB : Type uSB} {Cmd : Type uCmd} {Err : Type uErr}
    {Q : Type uQ} {R : Type uR}
    (Ref : SB → SA → Prop)
    (stepA : StepA SA Cmd Err)
    (stepB : StepB SB Cmd Err)
    (queryA : QueryA SA Q R)
    (queryB : QueryB SB Q R)
    (hStep : StepPreservation Ref stepA stepB)
    (hQuery : QueryPreservation Ref queryA queryB)
    {b0 : SB} {a0 : SA} {cmds : List Cmd} {bN : SB} {aN : SA}
    (hRef0 : Ref b0 a0)
    (hRunA : runA stepA a0 cmds = .ok aN)
    (hRunB : runB stepB b0 cmds = .ok bN) :
    Ref bN aN ∧ ∀ q, queryB bN q = queryA aN q := by
  induction cmds generalizing b0 a0 bN aN with
  | nil =>
      simp [runA, runB] at hRunA hRunB
      subst hRunA
      subst hRunB
      exact ⟨hRef0, fun q => hQuery.preserve hRef0⟩
  | cons c cs ih =>
      cases hAstep : stepA a0 c with
      | error e =>
          simp [runA, hAstep] at hRunA
      | ok a1 =>
          simp [runA, hAstep] at hRunA
          cases hBstep : stepB b0 c with
          | error e =>
              simp [runB, hBstep] at hRunB
          | ok b1run =>
              simp [runB, hBstep] at hRunB
              have hPres := hStep.success hRef0 hAstep
              rcases hPres with ⟨b1, hBok, hRef1⟩
              have hb1eq : b1 = b1run := by
                rw [hBstep] at hBok
                cases hBok
                rfl
              subst hb1eq
              have hTail := ih hRef1 hRunA hRunB
              rcases hTail with ⟨hRefN, hQueryN⟩
              exact ⟨hRefN, hQueryN⟩

end Framework
end DbAppVerification
