/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientCurve
public import FLT.Mazur.PolygonCompleteSmoothFieldSubgroup
public import FLT.Mazur.CompatibleSubgroupIdealIso
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# The original full field subgroup commutes with coefficient extension

The full DR coefficient comparison identifies the actual pulled-back complete
product ideal. Equality of these closed ideals recovers an isomorphism of the
original subgroup carriers, preserving their embeddings and group laws.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "H" => completeFieldFiniteSubgroup K n h L a ha p q hs
local notation "J" => completeFieldFiniteSubgroup K n h M aM haM r s ht
local notation "e" => completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht (0 : Fin n)

/-- The transported base change retains exactly the original complete product ideal. -/
theorem completeFieldCoefficientSubgroup_ideal :
    (((H).baseChange b).transport (e)).ideal = (J).ideal := by
  let A := (H).baseChange b
  let c := A.transportCompatibleIso (e)
  have hi := ideal_transport A _ c.curve c.subgroup c.compatible
  change _ = (A.ideal).comap (e).inv.curve.left at hi
  rw [show A.ideal = ((completeMarkingDivisor K n h).comap p).comap
      (pullback.fst q b) by
        rw [baseChange_ideal, completeFieldFiniteSubgroup_ideal]
        rfl] at hi
  rw [← Scheme.IdealSheafData.comap_comp,
    completeFieldCoefficientCurveIso_inv_fst, ← Scheme.IdealSheafData.comap_comp,
    completeCartesianBaseMap_fst] at hi
  exact hi.trans (completeFieldFiniteSubgroup_ideal K n h M aM haM r s ht).symm

/-- A full compatible comparison of the original actual finite subgroup schemes. -/
def completeFieldCoefficientSubgroupIso : CompatibleIso ((H).baseChange b) J :=
  (((H).baseChange b).transportCompatibleIso (e)).trans
    (compatibleIsoOfIdealEq _ _ (completeFieldCoefficientSubgroup_ideal K n h L a ha p q hs
      M r s ht))

/-- The comparison preserves the original full DR coefficient isomorphism. -/
theorem completeFieldCoefficientSubgroupIso_curve :
    (completeFieldCoefficientSubgroupIso K n h L a ha p q hs M r s ht).curve = e := by
  change (e) ≪≫ Iso.refl _ = e
  exact Iso.trans_refl _

end FLT.Mazur.PolygonInfinitesimalStages
