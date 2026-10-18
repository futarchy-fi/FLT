/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteParameterSubgroup
public import FLT.Mazur.OneGonCompleteSubgroupBaseChange
public import FLT.Mazur.CompatibleSubgroupIdealIso
public import FLT.Mazur.CompatibleSubgroupAmple

/-!
# The original closed subgroup is the actual complete-family specialization

The original faithful torus labels construct a subgroup on the actual closed
fiber. Equality of the full scheme-theoretic ideals gives a compatible subgroup
isomorphism, retaining its embedding and the entire generalized curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "H" => completeFiniteSubgroup K n labels hlabels

/-- The original closed torus labels as a subgroup of the actual closed generalized curve. -/
def completeClosedFiniteSubgroup : ((completeGeneralizedCurve K).baseChange (c)).FiniteSubgroup n :=
  completeParameterSubgroup K n (c) (closedCyclicParameter K n labels hlabels)

/-- Its whole-curve map is exactly the retained original closed subgroup map. -/
theorem completeClosedFiniteSubgroup_curveMap :
    (completeClosedFiniteSubgroup K n labels hlabels).curveMap =
      faithfulClosedCurveMap K n labels hlabels :=
  completeParameterSubgroup_curveMap K n (c) (closedCyclicParameter K n labels hlabels)

/-- The whole closed ideal is the actual original closed subgroup kernel. -/
theorem completeClosedFiniteSubgroup_ideal :
    (completeClosedFiniteSubgroup K n labels hlabels).ideal =
      (faithfulClosedCurveMap K n labels hlabels).left.ker := by
  unfold FiniteSubgroup.ideal
  rw [completeClosedFiniteSubgroup_curveMap]

/-- Specialization is compatible with the original whole curve and closed subgroup embedding. -/
def completeClosedSubgroupIso :
    CompatibleIso ((H).baseChange (c)) (completeClosedFiniteSubgroup K n labels hlabels) :=
  compatibleIsoOfIdealEq _ _ ((completeFiniteSubgroup_closed_ideal K n labels hlabels).trans
    (completeClosedFiniteSubgroup_ideal K n labels hlabels).symm)

/-- The comparison leaves the actual closed generalized curve unchanged. -/
theorem completeClosedSubgroupIso_curve :
    (completeClosedSubgroupIso K n labels hlabels).curve = Iso.refl _ := rfl

/-- Its subgroup isomorphism retains the original closed whole-curve embedding. -/
theorem completeClosedSubgroupIso_inclusion :
    (completeClosedSubgroupIso K n labels hlabels).subgroup.hom ≫
        faithfulClosedCurveMap K n labels hlabels = ((H).baseChange (c)).curveMap := by
  have hc := (completeClosedSubgroupIso K n labels hlabels).compatible
  rw [completeClosedSubgroupIso_curve, completeClosedFiniteSubgroup_curveMap] at hc
  change ((H).baseChange (c)).curveMap ≫ 𝟙 _ = _ at hc
  simpa only [Category.comp_id] using hc.symm

/-- The original closed subgroup is cyclic, with all original labels retained. -/
theorem completeClosedFiniteSubgroup_isCyclic :
    (completeClosedFiniteSubgroup K n labels hlabels).IsCyclic :=
  completeParameterSubgroup_isCyclic K n (c) (closedCyclicParameter K n labels hlabels)

/-- The original closed subgroup retains ampleness of the full complete divisor. -/
theorem completeClosedFiniteSubgroup_isAmple :
    (completeClosedFiniteSubgroup K n labels hlabels).IsAmple :=
  (completeClosedSubgroupIso K n labels hlabels).isAmple
    (completeFiniteSubgroup_baseChange_isAmple K n labels hlabels (c))

end FLT.Mazur.OneGonSmoothing
