/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteBoundaryTestMarking
public import FLT.Mazur.PolygonBoundaryCyclicSubgroup
public import FLT.Mazur.CyclicMarkingOrbitDivisor

/-!
# Actual boundary parameters recover the original complete-family subgroup

The subgroup constructed from the actual faithful boundary parameter has the
original complete product ideal. Its compatible isomorphism retains the full
complete-family curve, group law and subgroup embedding over the original test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonSmoothing
open CyclicBoundaryParameter GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup PolygonCyclicBoundary
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ PolygonSplitGroup.model K 1))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ PolygonSplitGroup.model K 1))
local notation "G" => PolygonSplitGroup.model K 1
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "hp" => OneGonGlobalPushout.isPushout K (by decide)
local notation "EC" => PolygonGeneralizedCurve.curve K 1 (by decide) p q hp
local notation "f" => completeBoundaryTestParameter K n labels hlabels g a b
local notation "J" => completePinchedFiniteSubgroup K n labels hlabels
local notation "hP" => completePinchedFiniteSubgroup_generator K n labels hlabels
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The actual cyclic parameter homomorphism is the original Cartier marking's pullback. -/
theorem completeBoundaryTestParameter_hom :
    cyclicSectionMarking (G) n g (f) =
      pullCyclicMarking (E := EC) g (completePinchedBoundaryMarking K n labels hlabels) := by
  apply MonoidHom.ext
  intro j
  rw [cyclicSectionMarking_apply, completeBoundaryTestParameter_section]
  rfl

/-- The actual parameter stays faithful on every nonempty boundary test. -/
theorem completeBoundaryTestParameter_distinct :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ cyclicSectionMarking (G) n g (f) (.ofAdd i)) := by
  rw [completeBoundaryTestParameter_hom]
  exact pullCyclicMarking_distinct (E := EC) g
    (completePinchedBoundaryMarking K n labels hlabels)
    (completePinchedBoundaryMarking_distinct K n labels hlabels)

local notation "hf" => completeBoundaryTestParameter_distinct K n labels hlabels g a b

/-- The product of all actual cyclic labels on the original pulled pinched curve. -/
def completeBoundaryTestIdeal : ((EC).baseChange g).curve.left.IdealSheafData :=
  ∏ i : Fin n, ((markedSection (G) n g (f) (1, 1, .ofAdd (i.val : ZMod n))) ≫
    ((EC).baseChange g).inclusion).left.ker

/-- The actual cyclic ideal is the entire original subgroup ideal after boundary pullback. -/
theorem completeBoundaryTestIdeal_eq :
    completeBoundaryTestIdeal K n labels hlabels g a b = ((J).baseChange g).ideal := by
  unfold completeBoundaryTestIdeal
  simp only [completeBoundaryTestParameter_generator]
  exact ((J).baseChange g).generatorCurveMarking_ideal ((EC).baseChange g)
    ((hP).baseChange J g)

/-- The actual subgroup built from the complete family's original boundary parameter. -/
def completeBoundaryTestSubgroup : ((EC).baseChange g).FiniteSubgroup n :=
  parameterSubgroup K 1 (by decide) p q hp n g (f) (hf)

/-- The actual parameter subgroup has exactly the original product of its cyclic labels. -/
theorem completeBoundaryTestSubgroup_ideal :
    (completeBoundaryTestSubgroup K n labels hlabels g a b).ideal =
      completeBoundaryTestIdeal K n labels hlabels g a b := by
  rw [completeBoundaryTestSubgroup, parameterSubgroup, relativeCyclicSubgroup_ideal]
  unfold completeBoundaryTestIdeal
  apply Finset.prod_congr rfl
  intro i _
  change ((ConstantCyclicGroup.component T n 1 ^ i.val) ≫
    ConstantCyclicSectionMap.toScheme (cyclicSectionMarking (G) n g (f)) ≫
      ((EC).baseChange g).inclusion).left.ker = _
  rw [← ConstantCyclicGenerator.component_natCast,
    ConstantCyclicSectionMap.component_toScheme_assoc, cyclicSectionMarking_apply]

/-- The parameter retains the actual original subgroup over its whole boundary curve. -/
def completeBoundaryTestClosedIso :
    CompatibleIso (completeBoundaryTestSubgroup K n labels hlabels g a b) ((J).baseChange g) :=
  compatibleIsoOfIdealEq _ _ ((completeBoundaryTestSubgroup_ideal K n labels hlabels g a b).trans
    (completeBoundaryTestIdeal_eq K n labels hlabels g a b))

/-- The actual boundary test recovers the full original complete-family subgroup data. -/
def completeBoundaryTestOriginalIso :
    CompatibleIso (completeBoundaryTestSubgroup K n labels hlabels g a b)
      ((completeFiniteSubgroup K n labels hlabels).baseChange (g ≫ c)) :=
  (completeBoundaryTestClosedIso K n labels hlabels g a b).trans
    (((completePinchedSubgroupIso K n labels hlabels).baseChange g).symm.trans
      (compatibleBaseChangeComp (completeFiniteSubgroup K n labels hlabels) (c) g).symm)

/-- The recovered subgroup keeps the original closed comparison and pullback composition. -/
theorem completeBoundaryTestOriginalIso_curve :
    (completeBoundaryTestOriginalIso K n labels hlabels g a b).curve =
      ((completePinchedSubgroupIso K n labels hlabels).baseChange g).curve.symm ≪≫
        ((completeGeneralizedCurve K).baseChangeCompIso (c) g).symm := by
  change Iso.refl _ ≪≫ (_ ≪≫ _) = _
  exact Iso.refl_trans _

/-- The actual constructed subgroup retains the full original divisor's ampleness. -/
theorem completeBoundaryTestSubgroup_isAmple :
    (completeBoundaryTestSubgroup K n labels hlabels g a b).IsAmple :=
  (completeBoundaryTestOriginalIso K n labels hlabels g a b).symm.isAmple
    (completeFiniteSubgroup_baseChange_isAmple K n labels hlabels (g ≫ c))

end FLT.Mazur.OneGonSmoothing
