/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteClosedCurveIso
public import FLT.Mazur.OneGonCompleteClosedSubgroupIso
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# The complete cyclic subgroup on the original pinched one-gon

The full DR comparison places the actual complete closed subgroup on the original
pinched polygon. It retains its carrier, generator, full ideal and ampleness.
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
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "hp" => OneGonGlobalPushout.isPushout K (by decide)
local notation "E" => PolygonGeneralizedCurve.curve K 1 (by decide) p q hp
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "H" => completeFiniteSubgroup K n labels hlabels
local notation "J" => FiniteSubgroup.baseChange (H) (c)
local notation "e" => Iso.symm (completeClosedCurveIso K)

/-- The actual complete closed subgroup, now on the original pinched generalized one-gon. -/
def completePinchedFiniteSubgroup : (E).FiniteSubgroup n := (J).transport (e)

/-- The comparison retains the full curve, group law and original subgroup embedding. -/
def completePinchedSubgroupIso :
    CompatibleIso (J) (completePinchedFiniteSubgroup K n labels hlabels) :=
  (J).transportCompatibleIso (e)

/-- The retained subgroup uses exactly the original closed whole-curve comparison. -/
theorem completePinchedSubgroupIso_curve :
    (completePinchedSubgroupIso K n labels hlabels).curve = (completeClosedCurveIso K).symm := rfl

/-- Its entire ideal is the original faithful closed ideal on the original pinched curve. -/
theorem completePinchedFiniteSubgroup_ideal :
    (completePinchedFiniteSubgroup K n labels hlabels).ideal =
      (faithfulClosedCurveMap K n labels hlabels).left.ker.comap
        (powerSeriesClosedFiberIso K).hom := by
  let d := completePinchedSubgroupIso K n labels hlabels
  have hi := ideal_transport (J) (completePinchedFiniteSubgroup K n labels hlabels)
    d.curve d.subgroup d.compatible
  rw [show d.curve = (e) from completePinchedSubgroupIso_curve K n labels hlabels] at hi
  change (completePinchedFiniteSubgroup K n labels hlabels).ideal =
    (J).ideal.comap (completeClosedCurveIso K).hom.curve.left at hi
  rw [completeFiniteSubgroup_closed_ideal, completeClosedCurveIso_curve] at hi
  exact hi

/-- The same original Cartier generator is retained on the pinched curve. -/
theorem completePinchedFiniteSubgroup_generator :
    (completePinchedFiniteSubgroup K n labels hlabels).IsCartierGenerator
      (GroupSectionBaseChange.pullSection (c) (completeFiniteGenerator K n labels hlabels)) :=
  (J).transport_cartierGenerator (e)
    ((completeFiniteGenerator_isCartierGenerator K n labels hlabels).baseChange (H) (c))

/-- The retained original pinched subgroup is cyclic. -/
theorem completePinchedFiniteSubgroup_isCyclic :
    (completePinchedFiniteSubgroup K n labels hlabels).IsCyclic :=
  (completePinchedFiniteSubgroup_generator K n labels hlabels).isCyclic _

/-- The original pinched subgroup retains the full complete divisor's ampleness. -/
theorem completePinchedFiniteSubgroup_isAmple :
    (completePinchedFiniteSubgroup K n labels hlabels).IsAmple :=
  (completePinchedSubgroupIso K n labels hlabels).isAmple
    (completeFiniteSubgroup_baseChange_isAmple K n labels hlabels (c))

end FLT.Mazur.OneGonSmoothing
