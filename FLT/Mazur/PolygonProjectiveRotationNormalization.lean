/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteProjectiveRotation
public import FLT.Mazur.WeierstrassAutomorphismNormalization

/-!
# The original projective rotation normalized at its retained marking

The infinity image is exactly the shifted original marking. Normalization
therefore constructs the actual residual group automorphism, whose triviality
is the remaining translation question.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeProjectiveRotationIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The actual image of infinity is the original marking with its shifted label. -/
@[reassoc] theorem completeProjectiveRotationIso_zero_image (i : Fin n) (b : ZMod n) :
    integralCurveZero (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) ≫
      (completeProjectiveRotationIso K n h L a ha p q hs i b).hom =
        (completeCartesianProjectiveMarkedPoint K n h L a ha p q hs i (rotateIndex b i)).left := by
  have he := completeProjectiveMarkedPoint_rotation K n h L a ha p q hs i i b
  rw [completeCartesianProjectiveMarkedPoint_self] at he
  change (Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ integralCurveZero _) ≫ _ = _ at he
  simpa using he

/-- The actual rotation leaves a canonical group automorphism after removing its infinity image. -/
def completeProjectiveRotationGroupPart (i : Fin n) (b : ZMod n) :
    integralCurveGroup (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i)
      (by
        let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
        exact WeierstrassCurve.isUnit_Δ _) ≅
    integralCurveGroup (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i)
      (by
        let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
        exact WeierstrassCurve.isUnit_Δ _) :=
  normalizedCurveGroupIso _ _ (completeProjectiveRotationIso K n h L a ha p q hs i b)
    (completeProjectiveRotationIso_over K n h L a ha p q hs i b)

/-- The residual group automorphism is the original normalized scheme morphism. -/
theorem completeProjectiveRotationGroupPart_hom (i : Fin n) (b : ZMod n) :
    (completeProjectiveRotationGroupPart K n h L a ha p q hs i b).hom.hom.hom.hom.left =
      (normalizedCurveIso _ (by
        let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
        exact WeierstrassCurve.isUnit_Δ _) (completeProjectiveRotationIso K n h L a ha p q hs i b)
        (completeProjectiveRotationIso_over K n h L a ha p q hs i b)).hom := rfl

end FLT.Mazur.PolygonInfinitesimalStages
