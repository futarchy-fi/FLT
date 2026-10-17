/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedCurveIso
public import FLT.Mazur.PolygonCompleteOriginalCyclicSubgroup
public import FLT.Mazur.PolygonCompleteClosedCartierGenerator
public import FLT.Mazur.CompatibleSubgroupIdealIso
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# The original closed subgroup is the actual complete-family pullback

Transport across the full DR comparison identifies the original complete product
ideal with its original closed-fiber ideal. The resulting compatible isomorphism
retains the actual closed divisor carrier and its embedding into the polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "b" => completeClosedBase K
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeClosedFiniteSubgroup K n h
local notation "e" => Iso.symm (completeClosedCurveIso K n h)

/-- The transported closed fiber has exactly the original closed product ideal. -/
theorem completeClosedSubgroup_transport_ideal :
    (((H).baseChange b).transport e).ideal = (J).ideal := by
  let A := (H).baseChange b
  let c := A.transportCompatibleIso e
  have hi := ideal_transport A _ c.curve c.subgroup c.compatible
  change _ = A.ideal.comap (completeClosedCurveIso K n h).hom.curve.left at hi
  rw [show A.ideal = (completeMarkingDivisor K n h).comap
      (pullback.fst (completeGeneralizedCurve K n h).curve.hom b) by
        rw [baseChange_ideal, completeOriginalFiniteSubgroup_ideal]] at hi
  rw [← Scheme.IdealSheafData.comap_comp, completeClosedCurveIso_fst] at hi
  exact hi.trans (completeClosedFiniteSubgroup_ideal K n h).symm

/-- The original complete subgroup specializes to the actual original closed subgroup. -/
def completeClosedSubgroupIso : CompatibleIso ((H).baseChange b) J :=
  (((H).baseChange b).transportCompatibleIso e).trans
    (compatibleIsoOfIdealEq _ _ (completeClosedSubgroup_transport_ideal K n h))

/-- The subgroup comparison uses the constructed full DR isomorphism. -/
theorem completeClosedSubgroupIso_curve : (completeClosedSubgroupIso K n h).curve = e := by
  change e ≪≫ Iso.refl _ = e
  exact Iso.trans_refl _

end FLT.Mazur.PolygonInfinitesimalStages
