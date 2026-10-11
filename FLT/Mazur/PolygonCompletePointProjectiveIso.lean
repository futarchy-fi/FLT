/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNonsingular
public import FLT.Mazur.PolygonCompletePointProjectiveExtension
public import FLT.Mazur.ProperDenseOpenIso
public import FLT.Mazur.WeierstrassIntegralDomain
public import FLT.Mazur.WeierstrassIntegralSmooth

/-!
# The original smooth fiber is its constructed projective cubic

The original affine isomorphism identifies a common dense open. Smoothness of
the actual nonsingular cubic supplies valuation stalks on the target too, so
proper extension constructs an inverse to the original projective morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The actual projective extension is an isomorphism on the original smooth field square. -/
theorem completeCartesianPointToProjective_isIso (i : Fin n) :
    IsIso (completeCartesianPointToProjective K n h L a ha p q hs i) := by
  let W := completeCartesianPointWeierstrass K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i
  let U := completeCartesianPointComplement K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i
  let _ := completeCartesianField_integral K n h L a ha p q hs
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from q]
    infer_instance
  let _ : W.IsElliptic := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
  let _ := integralCurveStructure_smooth_dimension W (WeierstrassCurve.isUnit_Δ W)
  let _ : (integralCurve W).IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (integralCurveStructure W)]
    infer_instance
  let _ : ∀ z : integralCurve W, ValuationRing ((integralCurve W).presheaf.stalk z) :=
    fun z ↦ smoothCurve_stalk_valuationRing (integralCurveStructure W) z
  let _ : IsDominant U.ι := Opens.isDominant_ι
    (completeCartesianSmoothPointComplement_dense K n h L a ha p q hs i)
  let _ : IsDominant (integralCurveChart W 2) := ⟨integralCurveAffine_denseRange W⟩
  let _ : IsDominant (monicToIntegralCurve W) := by
    unfold monicToIntegralCurve
    infer_instance
  let _ := completeCartesianSmoothPointToAffineCubic_isIso K n h L a ha p q hs i
  let _ : IsOpenImmersion (completeCartesianPointAffineToProjective K n h L a p q hs i) := by
    unfold completeCartesianPointAffineToProjective
    infer_instance
  let _ : IsDominant (completeCartesianPointAffineToProjective K n h L a p q hs i) := by
    unfold completeCartesianPointAffineToProjective
    infer_instance
  exact isIso_of_common_denseOpen q (integralCurveStructure W) U.ι
    (completeCartesianPointAffineToProjective K n h L a p q hs i) _
    (completeCartesianPointToProjective_over K n h L a ha p q hs i)
    (completeCartesianPointToProjective_restrict K n h L a ha p q hs i)

/-- The projective isomorphism retains the original constructed coordinate morphism. -/
def completeCartesianPointProjectiveIso (i : Fin n) :
    Y ≅ integralCurve (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i) := by
  let _ := completeCartesianPointToProjective_isIso K n h L a ha p q hs i
  exact asIso (completeCartesianPointToProjective K n h L a ha p q hs i)

/-- The projective isomorphism is over the unchanged specified field. -/
theorem completeCartesianPointProjectiveIso_over (i : Fin n) :
    (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom ≫
      integralCurveStructure (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) = q :=
  completeCartesianPointToProjective_over K n h L a ha p q hs i

end FLT.Mazur.PolygonInfinitesimalStages
