/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothOriginalCurveIso
public import FLT.Mazur.PolygonCompleteOriginalCyclicSubgroup
public import FLT.Mazur.PolygonCompleteSmoothFieldSubgroup
public import FLT.Mazur.CompatibleSubgroupIdealIso
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# The original smooth field subgroup is the actual complete-family pullback

Transport across the full smooth DR comparison retains the actual original
complete product ideal and its independently constructed field subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "b" => Spec.map (CommRingCat.ofHom a)
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeFieldFiniteSubgroup K n h L a ha p q hs
local notation "e" => Iso.symm (completeSmoothOriginalCurveIso K n h L a ha p q hs)

/-- The transported smooth fiber has exactly the original field product ideal. -/
theorem completeSmoothOriginalSubgroup_transport_ideal :
    (((H).baseChange b).transport e).ideal = (J).ideal := by
  let A := (H).baseChange b
  let c := A.transportCompatibleIso e
  have hi := ideal_transport A _ c.curve c.subgroup c.compatible
  change _ = A.ideal.comap (completeSmoothOriginalCurveIso K n h L a ha p q hs).hom.curve.left at hi
  rw [show A.ideal = (completeMarkingDivisor K n h).comap
      (pullback.fst (completeGeneralizedCurve K n h).curve.hom b) by
        rw [baseChange_ideal, completeOriginalFiniteSubgroup_ideal]] at hi
  rw [← Scheme.IdealSheafData.comap_comp, completeSmoothOriginalCurveIso_fst] at hi
  exact hi.trans (completeFieldFiniteSubgroup_ideal K n h L a ha p q hs).symm

/-- The original complete subgroup specializes to the actual original smooth field subgroup. -/
def completeSmoothOriginalSubgroupIso : CompatibleIso ((H).baseChange b) J :=
  (((H).baseChange b).transportCompatibleIso e).trans
    (compatibleIsoOfIdealEq _ _
      (completeSmoothOriginalSubgroup_transport_ideal K n h L a ha p q hs))

/-- The subgroup comparison uses the constructed full DR isomorphism. -/
theorem completeSmoothOriginalSubgroupIso_curve :
    (completeSmoothOriginalSubgroupIso K n h L a ha p q hs).curve = e := by
  change e ≪≫ Iso.refl _ = e
  exact Iso.trans_refl _

end FLT.Mazur.PolygonInfinitesimalStages
