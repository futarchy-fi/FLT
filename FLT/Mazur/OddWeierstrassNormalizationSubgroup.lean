/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizationCurve
public import FLT.Mazur.RetainedSubgroupCartierMarking
public import FLT.Mazur.CyclicMarkingDivisorTransport
public import FLT.Mazur.CompatibleSubgroupGeneratorMarking

/-!
# Retaining original cyclic subgroups under odd normalization

The full comparison carries the actual original subgroup, its Cartier generator,
and every repeated factor of its ideal. There is no etaleness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {n : ℕ} (H : (auxiliaryPullbackCurve g).FiniteSubgroup n)

/-- Normalize the original carrier and inclusion, without reconstructing an etale subgroup. -/
irreducible_def auxiliaryNormalizedSubgroup : (auxiliaryNormalizedCurve g).FiniteSubgroup n :=
  H.transport (auxiliaryNormalizationCurveIso g).symm

/-- The entire original subgroup has a compatible full-family comparison. -/
def auxiliaryNormalizedSubgroupIso : CompatibleIso H (auxiliaryNormalizedSubgroup g H) := by
  rw [auxiliaryNormalizedSubgroup_def]
  exact H.transportCompatibleIso (auxiliaryNormalizationCurveIso g).symm

/-- The normalized subgroup retains the full original ideal scheme-theoretically. -/
theorem auxiliaryNormalizedSubgroup_ideal :
    (auxiliaryNormalizedSubgroup g H).ideal =
      H.ideal.comap (auxiliaryNormalizationCurveIso g).hom.curve.left := by
  rw [auxiliaryNormalizedSubgroup_def]
  let a := H.transportCompatibleIso (auxiliaryNormalizationCurveIso g).symm
  exact ideal_transport H _ a.curve a.subgroup a.compatible

variable {P : 𝟙_ (Over (Spec (.of R))) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- The unchanged generator on the retained carrier remains Cartier. -/
theorem auxiliaryNormalizedSubgroup_generator :
    (auxiliaryNormalizedSubgroup g H).IsCartierGenerator
      (P ≫ (auxiliaryNormalizedSubgroupIso g H).subgroup.hom) :=
  (auxiliaryNormalizedSubgroupIso g H).cartierGenerator hP

variable [NeZero n]

/-- Normalization retains the cyclic marking of the actual original Cartier generator. -/
theorem auxiliaryNormalizedSubgroup_marking (i : Multiplicative (ZMod n)) :
    (auxiliaryNormalizedSubgroup g H).generatorCurveMarking
        (auxiliaryNormalizedSubgroup_generator g H hP) i =
      H.generatorCurveMarking hP i ≫ (auxiliaryNormalizedSubgroupIso g H).curve.hom.group :=
  (auxiliaryNormalizedSubgroupIso g H).generatorCurveMarking hP i

/-- Its orbit divisor contains every original factor, including coincident sections. -/
theorem auxiliaryNormalizedSubgroup_marking_ideal :
    (auxiliaryNormalizedCurve g).cyclicMarkingIdeal
      ((auxiliaryNormalizedSubgroup g H).generatorCurveMarking
        (auxiliaryNormalizedSubgroup_generator g H hP)) =
      H.ideal.comap (auxiliaryNormalizationCurveIso g).hom.curve.left := by
  exact ((auxiliaryNormalizedSubgroup g H).generatorCurveMarking_ideal
    (auxiliaryNormalizedCurve g) (auxiliaryNormalizedSubgroup_generator g H hP)).trans
      (auxiliaryNormalizedSubgroup_ideal g H)

end FLT.Mazur.OddWeierstrassParameter
