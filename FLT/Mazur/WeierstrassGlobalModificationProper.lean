/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationGluing
public import FLT.Mazur.SchemeOpenReplacementProper
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Properness of the entire modified projective cubic

The original Y-chart has its identity as full pullback, and the original
affine chart has the full proper local modification as pullback. Hence
the actual global contraction and its structure morphism are proper.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
open WeierstrassIntegralChart

/-- The entire original chart at infinity is unchanged by the global contraction. -/
theorem infinity_isPullback :
    IsPullback (𝟙 _) (infinityChart W s b3 b4 b6 h3 h4 h6 hs)
      (integralCurveChart W 1) (contraction W s b3 b4 b6 h3 h4 h6 hs) := by
  apply (SchemeOpenReplacement.isPullback_inl (affineBoundaryToY W) (overlapInclusion W 2 1)
    (boundary W s b3 b4 b6 h3 h4 h6 hs)
    (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6)
    (boundary_contraction W s b3 b4 b6 h3 h4 h6 hs)
    (boundary_preimage W s b3 b4 b6 h3 h4 h6 hs)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (yzPushoutIso W)
  · simp
  · simp [infinityChart]
  · simp
  · simp only [Iso.refl_hom, Category.id_comp, contraction]

/-- The inverse image of the entire original affine chart is the actual local modification. -/
theorem local_isPullback :
    IsPullback (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6)
      (localChart W s b3 b4 b6 h3 h4 h6 hs) (integralCurveChart W 2)
      (contraction W s b3 b4 b6 h3 h4 h6 hs) := by
  apply (SchemeOpenReplacement.isPullback_inr (affineBoundaryToY W) (overlapInclusion W 2 1)
    (boundary W s b3 b4 b6 h3 h4 h6 hs)
    (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6)
    (boundary_contraction W s b3 b4 b6 h3 h4 h6 hs)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (yzPushoutIso W)
  · simp
  · simp [localChart]
  · simp
  · simp only [Iso.refl_hom, Category.id_comp, contraction]

/-- The entire modified projective cubic contracts properly to the original cubic. -/
theorem contraction_isProper : IsProper (contraction W s b3 b4 b6 h3 h4 h6 hs) := by
  let _ := WeierstrassModificationReesCoordinates.affineContraction_isProper
    W s b3 b4 b6 h3 h4 h6 hs
  let _ := SchemeOpenReplacement.contraction_isProper (affineBoundaryToY W)
    (overlapInclusion W 2 1) (boundary W s b3 b4 b6 h3 h4 h6 hs)
    (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6)
    (boundary_contraction W s b3 b4 b6 h3 h4 h6 hs)
    (boundary_preimage W s b3 b4 b6 h3 h4 h6 hs)
  unfold contraction
  infer_instance

/-- The structure map of the actual whole projective modification over the original base. -/
def structureMap : model W s b3 b4 b6 h3 h4 h6 hs ⟶ Spec (.of R) :=
  contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W

/-- The constructed entire projective model is proper over the original base. -/
instance structureMap_isProper : IsProper (structureMap W s b3 b4 b6 h3 h4 h6 hs) := by
  let _ := contraction_isProper W s b3 b4 b6 h3 h4 h6 hs
  unfold structureMap
  infer_instance

end FLT.Mazur.WeierstrassGlobalModification
