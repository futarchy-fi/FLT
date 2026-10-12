/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFixedPointFree
public import FLT.Mazur.PolygonCompleteProjectiveRotation

/-!
# Fixed-point freeness on the original chosen fibers and cubics

The original cartesian projection and projective isomorphism retain absence
of invariant maps from every nonempty test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeCartesianRotation completeProjectiveRotationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every original cartesian fiber action has no invariant nonempty test morphism. -/
theorem completeCartesianRotation_comp_ne {S Y T : Scheme} [Nonempty T]
    (s : S ⟶ Spec (.of (PowerSeries K)))
    (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
    (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)
    (t : T ⟶ Y) (a : ZMod n) (ha : a ≠ 0) :
    t ≫ completeCartesianRotation K n h s p q hs a ≠ t := by
  intro he
  apply completeRotation_comp_ne K n h (t ≫ p) a ha
  have hc := congrArg (· ≫ p) he
  simpa only [Category.assoc, completeCartesianRotation_fst] using hc

/-- The constructed projective cubic action has no invariant nonempty test morphism. -/
theorem completeProjectiveRotation_comp_ne
    (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
    {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom a)))
    (i : Fin n) {T : Scheme} [Nonempty T]
    (t : T ⟶ integralCurve (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i)) (b : ZMod n) (hb : b ≠ 0) :
    t ≫ (completeProjectiveRotationIso K n h L a ha p q hs i b).hom ≠ t := by
  intro he
  let e := completeCartesianPointProjectiveIso K n h L a ha p q hs i
  apply completeCartesianRotation_comp_ne K n h (Spec.map (CommRingCat.ofHom a))
    p q hs (t ≫ e.inv) b hb
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, Category.assoc, ← completePointProjectiveIso_rotation,
    ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
    he, Category.assoc, e.inv_hom_id, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
