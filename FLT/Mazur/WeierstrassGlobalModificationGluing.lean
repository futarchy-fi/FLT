/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationOriginalOpen
public import FLT.Mazur.WeierstrassIntegralCurvePushout
public import FLT.Mazur.SchemeOpenReplacementPreimage

/-!
# Gluing the actual modification into the whole projective cubic

The unchanged Y-chart contains the point at infinity. Its overlap with the
original affine cubic is D(y), which is unchanged by the actual local
modification. Gluing on this full overlap gives the whole projective model.
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

/-- The unchanged D(y) boundary inside the actual equation modification. -/
def boundary : overlapScheme W 2 1 ⟶ WeierstrassModificationX.modification W s b3 b4 b6 :=
  WeierstrassModificationReesCoordinates.originalOpen W s b3 b4 b6 h3 h4 h6 hs
    (coord W 2 1) (Ideal.subset_span (by simp))

instance boundary_isOpenImmersion : IsOpenImmersion (boundary W s b3 b4 b6 h3 h4 h6 hs) := by
  unfold boundary
  infer_instance

/-- The original overlap retains precisely its original affine-cubic coordinates. -/
@[reassoc] theorem boundary_contraction :
    boundary W s b3 b4 b6 h3 h4 h6 hs ≫
        WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6 =
      overlapInclusion W 2 1 :=
  WeierstrassModificationReesCoordinates.originalOpen_affineContraction
    W s b3 b4 b6 h3 h4 h6 hs _ _

/-- The complete original overlap is unchanged under the actual affine contraction. -/
theorem boundary_preimage :
    (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6) ⁻¹'
        Set.range (overlapInclusion W 2 1) =
      Set.range (boundary W s b3 b4 b6 h3 h4 h6 hs) :=
  WeierstrassModificationReesCoordinates.originalOpen_preimage W s b3 b4 b6 h3 h4 h6 hs _ _

/-- The whole modified cubic, including the unchanged original chart at infinity. -/
def model : Scheme :=
  pushout (affineBoundaryToY W) (boundary W s b3 b4 b6 h3 h4 h6 hs)

/-- The original Y-chart embeds openly into the whole modified cubic. -/
def infinityChart : chartScheme W 1 ⟶ model W s b3 b4 b6 h3 h4 h6 hs := pushout.inl _ _

/-- The whole actual equation modification embeds openly into the global model. -/
def localChart : WeierstrassModificationX.modification W s b3 b4 b6 ⟶
    model W s b3 b4 b6 h3 h4 h6 hs := pushout.inr _ _

instance infinityChart_isOpenImmersion :
    IsOpenImmersion (infinityChart W s b3 b4 b6 h3 h4 h6 hs) := by
  unfold infinityChart
  infer_instance

instance localChart_isOpenImmersion :
    IsOpenImmersion (localChart W s b3 b4 b6 h3 h4 h6 hs) := by
  unfold localChart
  infer_instance

/-- The actual whole contraction to the same original projective cubic. -/
def contraction : model W s b3 b4 b6 h3 h4 h6 hs ⟶ integralCurve W :=
  SchemeOpenReplacement.contraction (affineBoundaryToY W) (overlapInclusion W 2 1)
    (boundary W s b3 b4 b6 h3 h4 h6 hs)
    (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6)
    (boundary_contraction W s b3 b4 b6 h3 h4 h6 hs) ≫ (yzPushoutIso W).hom

/-- The global contraction is unchanged on the original chart at infinity. -/
@[reassoc] theorem infinityChart_contraction :
    infinityChart W s b3 b4 b6 h3 h4 h6 hs ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      integralCurveChart W 1 := by
  rw [infinityChart, contraction, SchemeOpenReplacement.inl_contraction_assoc, inl_yzPushoutIso]

/-- The global contraction retains the existing actual local equation contraction. -/
@[reassoc] theorem localChart_contraction :
    localChart W s b3 b4 b6 h3 h4 h6 hs ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 := by
  rw [localChart, contraction, SchemeOpenReplacement.inr_contraction_assoc,
    inr_yzPushoutIso, WeierstrassModificationX.affineContraction_toCurve]

/-- Both actual pieces cover the entire modified projective cubic. -/
theorem charts_cover (z : model W s b3 b4 b6 h3 h4 h6 hs) :
    (∃ a, infinityChart W s b3 b4 b6 h3 h4 h6 hs a = z) ∨
      ∃ a, localChart W s b3 b4 b6 h3 h4 h6 hs a = z :=
  SchemeOpenPushout.charts_cover _ _ z

end FLT.Mazur.WeierstrassGlobalModification
