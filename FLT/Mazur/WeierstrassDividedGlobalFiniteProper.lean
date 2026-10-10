/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteGluing
public import FLT.Mazur.SchemeOpenReplacementProper
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Properness of every entire finite projective model

The original Y-chart has its identity as full pullback, and the original
affine chart has the full proper local modification as pullback. Hence
the actual global contraction and its structure morphism are proper.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart

/-- The entire original chart at infinity is unchanged by the global contraction. -/
theorem finiteInfinity_isPullback :
    IsPullback (𝟙 _) (finiteInfinityChart hπ data j hj)
      (integralCurveChart W 1) (finiteGlobalContraction hπ data j hj) := by
  apply (SchemeOpenReplacement.isPullback_inl (affineBoundaryToY W) (overlapInclusion W 2 1)
    (finiteYBoundary hπ data j hj)
    (finiteToAffine hπ data j hj)
    (finiteYBoundary_contraction hπ data j hj)
    (finiteYBoundary_preimage hπ data j hj)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (yzPushoutIso W)
  · simp
  · simp [finiteInfinityChart]
  · simp
  · simp only [Iso.refl_hom, Category.id_comp, finiteGlobalContraction]

/-- The inverse image of the entire original affine chart is the actual local modification. -/
theorem finiteLocal_isPullback :
    IsPullback (finiteToAffine hπ data j hj)
      (finiteLocalChart hπ data j hj) (integralCurveChart W 2)
      (finiteGlobalContraction hπ data j hj) := by
  apply (SchemeOpenReplacement.isPullback_inr (affineBoundaryToY W) (overlapInclusion W 2 1)
    (finiteYBoundary hπ data j hj)
    (finiteToAffine hπ data j hj)
    (finiteYBoundary_contraction hπ data j hj)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (yzPushoutIso W)
  · simp
  · simp [finiteLocalChart]
  · simp
  · simp only [Iso.refl_hom, Category.id_comp, finiteGlobalContraction]

/-- The entire modified projective cubic contracts properly to the original cubic. -/
theorem finiteGlobalContraction_isProper : IsProper (finiteGlobalContraction hπ data j hj) := by
  let _ := finiteToAffine_isProper hπ data j hj
  let _ := SchemeOpenReplacement.contraction_isProper (affineBoundaryToY W)
    (overlapInclusion W 2 1) (finiteYBoundary hπ data j hj)
    (finiteToAffine hπ data j hj)
    (finiteYBoundary_contraction hπ data j hj)
    (finiteYBoundary_preimage hπ data j hj)
  unfold finiteGlobalContraction
  infer_instance

/-- The structure map of the actual whole projective modification over the original base. -/
def finiteGlobalStructure : finiteGlobalModel hπ data j hj ⟶ Spec (.of R) :=
  finiteGlobalContraction hπ data j hj ≫ integralCurveStructure W

/-- The constructed entire projective model is proper over the original base. -/
instance finiteGlobalStructure_isProper : IsProper (finiteGlobalStructure hπ data j hj) := by
  let _ := finiteGlobalContraction_isProper hπ data j hj
  unfold finiteGlobalStructure
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
