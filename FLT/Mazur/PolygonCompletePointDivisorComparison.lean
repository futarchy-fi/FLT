/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointInfinity
public import FLT.Mazur.WeierstrassOriginIdealSheaf

/-!
# The original marked divisor under the projective comparison

The pointed isomorphism pulls the actual origin ideal back to the original
retained marking ideal. All infinitesimal powers are preserved as ideal sheaves,
not merely their topological supports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The projective comparison pulls the actual origin ideal back to the retained marking ideal. -/
theorem completeCartesianPointToProjective_originIdeal (i : Fin n) :
    (integralCurveZero (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i)).ker.comap
      (completeCartesianPointToProjective K n h L a ha p q hs i) =
      (completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs i).ker := by
  let _ := completeCartesianPointToProjective_isIso K n h L a ha p q hs i
  have hc : IsClosedImmersion (completeCartesianMarking K n h
      (Spec.map (CommRingCat.ofHom a)) p q hs i ≫
        completeCartesianPointToProjective K n h L a ha p q hs i) := by
    rw [completeCartesianPointToProjective_marking]
    infer_instance
  rw [← completeCartesianPointToProjective_marking K n h L a ha p q hs i,
    ProjectiveLineMarkedCharts.ker_comap_mono]

/-- Every infinitesimal marked-point power is retained by the original projective isomorphism. -/
theorem completeCartesianPointToProjective_originIdealPower (i : Fin n) (m : ℕ) :
    ((integralCurveZero (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i)).ker ^ m).comap
      (completeCartesianPointToProjective K n h L a ha p q hs i) =
      (completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs i).ker ^ m := by
  rw [FCurve.idealSheaf_comap_pow, completeCartesianPointToProjective_originIdeal]

end FLT.Mazur.PolygonInfinitesimalStages
