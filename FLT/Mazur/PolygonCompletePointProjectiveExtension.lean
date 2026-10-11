/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothPointAffine
public import FLT.Mazur.ProperDenseOpenExtension
public import FLT.Mazur.SmoothCurveValuationStalk
public import FLT.Mazur.WeierstrassIntegralProper
public import FLT.Mazur.WeierstrassMonicOpenImmersion

/-!
# Extending the original affine comparison across its retained point

The nonzero-parameter original square is an integral smooth curve. Its actual
valuation stalks extend the existing coordinate morphism to the original
projective Weierstrass cubic, uniquely over the specified field.
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

/-- The original affine coordinate map, followed by the actual projective chart inclusion. -/
def completeCartesianPointAffineToProjective (i : Fin n) :
    (completeCartesianPointComplement K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).toScheme ⟶
      integralCurve (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) :=
  completeCartesianPointToAffineCubic K n h L _ p q hs i ≫
    monicToIntegralCurve _

/-- The affine map into the actual projective cubic lies over the original field. -/
theorem completeCartesianPointAffineToProjective_over (i : Fin n) :
    completeCartesianPointAffineToProjective K n h L a p q hs i ≫
      integralCurveStructure (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) =
      (completeCartesianPointComplement K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i).ι ≫ q := by
  rw [completeCartesianPointAffineToProjective, Category.assoc, monicToIntegralCurve_over]
  exact completeCartesianPointToAffineCubic_over K n h L _ p q hs i

include ha in
/-- The actual retained-point complement is dense on every original smooth field square. -/
theorem completeCartesianSmoothPointComplement_dense (i : Fin n) :
    Dense ((completeCartesianPointComplement K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i) : Set Y) := by
  let _ := completeCartesianField_integral K n h L a ha p q hs
  let U := completeCartesianPointComplement K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i
  let e := completeCartesianSmoothPointAffineIso K n h L a ha p q hs i
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of
    (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).toAffine.CoordinateRing)))
  exact U.2.dense ⟨(e.inv z).1, (e.inv z).2⟩

include ha in
/-- The original affine coordinate morphism extends uniquely across the retained point. -/
theorem completeCartesianPoint_existsUnique_projectiveExtension (i : Fin n) :
    ∃! f : Y ⟶ integralCurve (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i),
      f ≫ integralCurveStructure (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) = q ∧
      (completeCartesianPointComplement K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i).ι ≫ f =
          completeCartesianPointAffineToProjective K n h L a p q hs i := by
  let _ := completeCartesianField_integral K n h L a ha p q hs
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from q]
    infer_instance
  let _ : ∀ y : Y, ValuationRing (Y.presheaf.stalk y) :=
    fun y ↦ smoothCurve_stalk_valuationRing q y
  exact existsUnique_denseOpen_extension_of_valuation_stalks q _ _
    (completeCartesianSmoothPointComplement_dense K n h L a ha p q hs i) _
    (completeCartesianPointAffineToProjective_over K n h L a p q hs i)

/-- The extension of the original coordinate map into its actual projective cubic. -/
def completeCartesianPointToProjective (i : Fin n) :
    Y ⟶ integralCurve (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i) :=
  (completeCartesianPoint_existsUnique_projectiveExtension K n h L a ha p q hs i).choose

/-- The constructed extension lies over the original field map. -/
theorem completeCartesianPointToProjective_over (i : Fin n) :
    completeCartesianPointToProjective K n h L a ha p q hs i ≫
      integralCurveStructure (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) = q :=
  (completeCartesianPoint_existsUnique_projectiveExtension
    K n h L a ha p q hs i).choose_spec.1.1

/-- Its restriction is exactly the original coordinate morphism into the affine chart. -/
theorem completeCartesianPointToProjective_restrict (i : Fin n) :
    (completeCartesianPointComplement K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).ι ≫
        completeCartesianPointToProjective K n h L a ha p q hs i =
      completeCartesianPointAffineToProjective K n h L a p q hs i :=
  (completeCartesianPoint_existsUnique_projectiveExtension
    K n h L a ha p q hs i).choose_spec.1.2

end FLT.Mazur.PolygonInfinitesimalStages
