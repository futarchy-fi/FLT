/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothPointAffine
public import FLT.Mazur.WeierstrassAffineSmoothDiscriminant

/-!
# Nonsingularity of the original pointed Weierstrass equation

The actual affine complement isomorphism transports smoothness over the specified
field to the monic cubic. The geometric singular-point obstruction then forces
the original equation's discriminant to be nonzero, in every characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

include ha in
/-- The original monic affine cubic is smooth over its original field. -/
theorem completeCartesianPointMonic_smooth (i : Fin n) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap L
      (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i).toAffine.CoordinateRing))) := by
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ := SmoothOfRelativeDimension.smooth 1 q
  let e := completeCartesianSmoothPointAffineIso K n h L a ha p q hs i
  have he := completeCartesianSmoothPointAffineIso_over K n h L a ha p q hs i
  have hu : Smooth (e.inv ≫
      (completeCartesianPointComplement K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i).ι ≫ q) := inferInstance
  rw [← he, Iso.inv_hom_id_assoc] at hu
  exact hu

include ha in
/-- The constructed pointed equation is elliptic on every original smooth field square. -/
theorem completeCartesianPointWeierstrass_isElliptic (i : Fin n) :
    (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).IsElliptic := by
  let _ := completeCartesianPointMonic_smooth K n h L a ha p q hs i
  exact WeierstrassIntegralChart.isElliptic_of_smooth_monic _

include ha in
/-- Its actual discriminant is nonzero, with no new field or perfection hypothesis. -/
theorem completeCartesianPointWeierstrass_discriminant_ne_zero (i : Fin n) :
    (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).Δ ≠ 0 := by
  let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
  exact isUnit_iff_ne_zero.mp (WeierstrassCurve.isUnit_Δ _)

end FLT.Mazur.PolygonInfinitesimalStages
