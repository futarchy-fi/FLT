/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHigherPairedStability
public import FLT.Mazur.PolygonSmoothingStationaryNodes

/-!
# Whole-node stabilization of higher arithmetic corrections

Joint detection on the two punctures proves that every full factor is the
canonical identification of its equal smoothing parameters. This includes
reflection, both-branch composition, rebasing, and the inverse terminal map.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)
  (m r : ℕ) (hm : m ≤ r) (t : Quotient R π m)

/-- The whole higher node factor stabilizes, not just a chosen outgoing coordinate. -/
theorem correctionNodeFactor_higher_stable (q : R[T;T⁻¹]) :
    correctionNodeFactor R π m t (higherCorrectionField R π r q) =
      nodeParameterEquiv _ t (correctionSmoothing_higher_stable R π m r hm t q) := by
  apply nodeFactor_eq_parameter_of_punctures
  intro b
  rw [correctionNodeFactor_puncture, correctionPunctureFactor_higher_stable R π m r hm]
  rfl

/-- Reflection preserves the complete equal-parameter node identification. -/
theorem reflectedCorrectionNodeFactor_higher_stable (q : R[T;T⁻¹]) :
    reflectedCorrectionNodeFactor R π m t (higherCorrectionField R π r q) =
      nodeParameterEquiv _ t (correctionSmoothing_higher_stable R π m r hm t q) := by
  apply nodeFactor_eq_parameter_of_punctures
  intro b
  rw [reflectedCorrectionNodeFactor_puncture,
    correctionPunctureFactor_higher_stable R π m r hm]
  rfl

local notation "v" q => fun b ↦ higherCorrectionField R π r (q b)

/-- The paired whole-node correction is the canonical parameter identification. -/
theorem twoBranchCorrectionNodeFactor_higher_stable (q : Bool → R[T;T⁻¹]) :
    twoBranchCorrectionNodeFactor R π m t (v q) =
      nodeParameterEquiv _ t (twoBranchCorrectionSmoothing_higher_stable R π m r hm t q) := by
  apply nodeFactor_eq_parameter_of_punctures
  intro b
  rw [twoBranchCorrectionNodeFactor_puncture,
    twoBranchCorrectionPunctureFactor_higher_stable R π m r hm]
  rfl

/-- The positive rebased factor is the entire original node identification. -/
theorem twoBranchCorrectionRebasedFactor_higher_stable (q : Bool → R[T;T⁻¹]) :
    twoBranchCorrectionRebasedFactor R π m t (v q) =
      nodeParameterEquiv t _
        (twoBranchCorrectionRebasedSmoothing_higher_stable R π m r hm t q).symm := by
  apply nodeFactor_eq_parameter_of_punctures
  intro b
  rw [twoBranchCorrectionRebasedFactor_puncture,
    twoBranchCorrectionRebasedPunctureFactor_higher_stable R π m r hm]
  rfl

/-- The full inverse terminal correction is also the canonical node identification. -/
theorem twoBranchCorrectionRebasedFactor_higher_symm_stable (q : Bool → R[T;T⁻¹]) :
    (twoBranchCorrectionRebasedFactor R π m t (v q)).symm =
      nodeParameterEquiv _ t
        (twoBranchCorrectionRebasedSmoothing_higher_stable R π m r hm t q) := by
  apply nodeFactor_eq_parameter_of_punctures
  intro b
  rw [twoBranchCorrectionRebasedFactor_symm_puncture,
    twoBranchCorrectionRebasedPunctureFactor_higher_symm_stable R π m r hm]
  rfl

end FLT.Mazur.PolygonArithmeticStages
