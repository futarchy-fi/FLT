/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousStep
public import FLT.Mazur.PolygonArithmeticHigherNodeStability

/-!
# Every simultaneous correction stabilizes all earlier arithmetic layers

The actual initial, shared last, and rebased terminal smoothings are unchanged.
Both complete residuals and the whole node factors keep their original values.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
  (S : State R π) (r : ℕ) (q : Bool → Bool → R[T;T⁻¹]) (m : ℕ) (hm : m ≤ r)

include hm

/-- A later simultaneous step preserves the actual earlier initial smoothing. -/
theorem State.step_initial_stable (b : Bool) :
    (S.step r q).initial m b = S.initial m b :=
  correctionSmoothing_higher_stable R π m r hm _ _

/-- The shared last smoothing retains its full value on every earlier quotient. -/
theorem State.step_last_stable (b : Bool) :
    (S.step r q).last m b = S.last m b :=
  twoBranchCorrectionSmoothing_higher_stable R π m r hm _ _

/-- Rebasing leaves the common earlier terminal smoothing unchanged. -/
theorem State.step_terminal_stable : (S.step r q).terminal m = S.terminal m :=
  twoBranchCorrectionRebasedSmoothing_higher_stable R π m r hm _ _

/-- The entire initial edge, including its reciprocal base, is stationary. -/
theorem State.step_initialEquiv_stable (b : Bool) :
    (S.step r q).initialEquiv m b = S.initialEquiv m b := by
  change ((twoBranchCorrectionPunctureFactor R π m _ _ _).trans _).trans _ = _
  unfold lastInput initialInput
  rw [twoBranchCorrectionPunctureFactor_higher_stable R π m r hm,
    correctionPunctureFactor_higher_stable R π m r hm]
  rfl

/-- The whole last factor is stationary in the inverse closing coordinate too. -/
theorem State.lastEdge_stable (b : Bool) : S.lastEdge r q m b = AlgEquiv.refl := by
  unfold State.lastEdge lastInput
  rw [twoBranchCorrectionPunctureFactor_higher_stable R π m r hm]
  ext z : 1
  exact involutive_invert z

/-- Both closing residuals retain their entire earlier values. -/
theorem State.step_closingEquiv_stable (b : Bool) :
    (S.step r q).closingEquiv m b = S.closingEquiv m b := by
  change ((twoBranchCorrectionRebasedPunctureFactor R π m _ _ b).symm.trans _).trans _ = _
  unfold terminalInput
  rw [twoBranchCorrectionRebasedPunctureFactor_higher_stable R π m r hm,
    State.lastEdge_stable S r q m hm]
  rfl

/-- The actual initial whole-node factor is the canonical equal-parameter map. -/
theorem State.initialFactor_stable (b : Bool) :
    S.initialFactor r q m b = nodeParameterEquiv _ _ (S.step_initial_stable r q m hm b) :=
  correctionNodeFactor_higher_stable R π m r hm _ _

/-- The same canonical whole-node map serves both earlier last edges. -/
theorem State.lastFactor_stable (b : Bool) :
    S.lastFactor r q m b = nodeParameterEquiv _ _ (S.step_last_stable r q m hm b) :=
  twoBranchCorrectionNodeFactor_higher_stable R π m r hm _ _

/-- The full common terminal factor retains its original rebasing orientation. -/
theorem State.terminalFactor_stable :
    S.terminalFactor r q m = nodeParameterEquiv _ _ (S.step_terminal_stable r q m hm).symm :=
  twoBranchCorrectionRebasedFactor_higher_stable R π m r hm _ _

end FLT.Mazur.PolygonArithmeticSimultaneous
