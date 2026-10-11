/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIrreducibleAffine
public import FLT.Mazur.PolygonCompleteSmoothIrreducible

/-!
# The actual affine cubic isomorphism on smooth original fibers

Nonvanishing of the original parameter now constructs all the geometry needed
by the existing affine comparison. The isomorphism uses the same coordinate map
and the same specified field square and retains the chosen point label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

include ha in
/-- The actual point line is ample on every nonzero-parameter original square. -/
theorem completeCartesianSmoothPointLine_ample (i : Fin n) :
    AmpleLineBundle
      (completeCartesianPointLine K n h (Spec.map (CommRingCat.ofHom a)) p q hs i) := by
  let _ := completeCartesianField_irreducible K n h L a ha p q hs
  exact completeCartesianPointLine_ample_of_irreducible K n h L _ p q hs i

include ha in
/-- The existing original affine coordinate map is an isomorphism on the smooth square. -/
theorem completeCartesianSmoothPointToAffineCubic_isIso (i : Fin n) :
    IsIso (completeCartesianPointToAffineCubic K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i) := by
  let _ := completeCartesianField_irreducible K n h L a ha p q hs
  exact completeCartesianPointToAffineCubic_isIso_of_irreducible K n h L _ p q hs i

/-- The constructed affine comparison needs only the actual nonzero parameter. -/
def completeCartesianSmoothPointAffineIso (i : Fin n) :
    (completeCartesianPointComplement K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).toScheme ≅
      Spec (.of (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i).toAffine.CoordinateRing) := by
  let _ := completeCartesianSmoothPointToAffineCubic_isIso K n h L a ha p q hs i
  exact asIso (completeCartesianPointToAffineCubic K n h L _ p q hs i)

/-- The smooth affine isomorphism lies over the unchanged original field. -/
theorem completeCartesianSmoothPointAffineIso_over (i : Fin n) :
    (completeCartesianSmoothPointAffineIso K n h L a ha p q hs i).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap L
        (completeCartesianPointWeierstrass K n h L
          (Spec.map (CommRingCat.ofHom a)) p q hs i).toAffine.CoordinateRing)) =
      (completeCartesianPointComplement K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i).ι ≫ q :=
  completeCartesianPointToAffineCubic_over K n h L _ p q hs i

end FLT.Mazur.PolygonInfinitesimalStages
