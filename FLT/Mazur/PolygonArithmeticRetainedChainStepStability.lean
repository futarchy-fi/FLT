/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainStep
public import FLT.Mazur.PolygonArithmeticHigherNodeStability

/-!
# Every full-chain correction stabilizes all earlier arithmetic layers

The actual initial, retained, and rebased terminal smoothings are unchanged.
All complete residuals and the whole node factors keep their original values.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (S : State R π n) (r : ℕ) (q : Edge n → Bool → R[T;T⁻¹]) (m : ℕ) (hm : m ≤ r)

include hm

/-- A later simultaneous step preserves the actual earlier initial smoothing. -/
theorem State.step_initial_stable (b : Bool) :
    (S.step r q).initial m b = S.initial m b :=
  correctionSmoothing_higher_stable R π m r hm _ _

/-- The retained smoothing retains its full value on every earlier quotient. -/
theorem State.step_retained_stable (i : Fin (n + 1)) (b : Bool) :
    (S.step r q).retained m i b = S.retained m i b :=
  twoBranchCorrectionSmoothing_higher_stable R π m r hm _ _

/-- Rebasing leaves the common earlier terminal smoothing unchanged. -/
theorem State.step_terminal_stable : (S.step r q).terminal m = S.terminal m :=
  twoBranchCorrectionRebasedSmoothing_higher_stable R π m r hm _ _

/-- Every whole outgoing puncture is stationary in its edge coordinate too. -/
theorem State.outgoingFactor_stable (i : Fin (n + 1)) (b : Bool) :
    S.outgoingFactor r q m i b = AlgEquiv.refl := by
  unfold State.outgoingFactor retainedInput
  rw [twoBranchCorrectionPunctureFactor_higher_stable R π m r hm]
  ext z : 1
  exact involutive_invert z

/-- Every complete internal or boundary edge is stationary on earlier quotients. -/
theorem State.step_edgeEquiv_stable (e : Edge n) (b : Bool) :
    (S.step r q).edgeEquiv e m b = S.edgeEquiv e m b := by
  cases e with
  | initial =>
    change ((twoBranchCorrectionPunctureFactor R π m _ _ _).trans _).trans _ = _
    unfold retainedInput initialInput
    rw [twoBranchCorrectionPunctureFactor_higher_stable R π m r hm,
      correctionPunctureFactor_higher_stable R π m r hm]
    rfl
  | incoming i =>
    change ((twoBranchCorrectionPunctureFactor R π m _ _ _).trans _).trans _ = _
    rw [State.outgoingFactor_stable S r q m hm]
    unfold retainedInput
    rw [twoBranchCorrectionPunctureFactor_higher_stable R π m r hm]
    rfl
  | closing =>
    change ((twoBranchCorrectionRebasedPunctureFactor R π m _ _ b).symm.trans _).trans _ = _
    unfold terminalInput
    rw [twoBranchCorrectionRebasedPunctureFactor_higher_stable R π m r hm,
      State.outgoingFactor_stable S r q m hm]
    rfl

/-- The actual initial whole-node factor is the canonical equal-parameter map. -/
theorem State.initialFactor_stable (b : Bool) :
    S.initialFactor r q m b = nodeParameterEquiv _ _ (S.step_initial_stable r q m hm b) :=
  correctionNodeFactor_higher_stable R π m r hm _ _

/-- The same canonical whole-node map serves both earlier retained edges. -/
theorem State.retainedFactor_stable (i : Fin (n + 1)) (b : Bool) :
    S.retainedFactor r q m i b = nodeParameterEquiv _ _ (S.step_retained_stable r q m hm i b) :=
  twoBranchCorrectionNodeFactor_higher_stable R π m r hm _ _

/-- The full common terminal factor retains its original rebasing orientation. -/
theorem State.terminalFactor_stable :
    S.terminalFactor r q m = nodeParameterEquiv _ _ (S.step_terminal_stable r q m hm).symm :=
  twoBranchCorrectionRebasedFactor_higher_stable R π m r hm _ _

end FLT.Mazur.PolygonArithmeticRetainedChain
