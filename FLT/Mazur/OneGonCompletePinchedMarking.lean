/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompletePinchedSubgroup

/-!
# Faithful Cartier markings on the original pinched one-gon

The actual complete generator labels pull back and transport to the original
polygon group. All labels retain their original values and universal distinctness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "G" => PolygonSplitGroup.model K 1
local notation "J" => completePinchedFiniteSubgroup K n labels hlabels
local notation "hP" => completePinchedFiniteSubgroup_generator K n labels hlabels

/-- The original Cartier generator labels in the original pinched polygon group. -/
def completePinchedBoundaryMarking : Multiplicative (ZMod n) →* (𝟙_ (Over (Spec (.of K))) ⟶ G) :=
  (J).generatorCurveMarking (hP)

local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "H" => completeFiniteSubgroup K n labels hlabels

/-- The complete Cartier generator marking is the original lifted cyclic labeling. -/
theorem completeFiniteGenerator_marking (j : Multiplicative (ZMod n)) :
    (H).generatorCurveMarking (completeFiniteGenerator_isCartierGenerator K n labels hlabels) j =
      faithfulCompleteMarking K n labels hlabels j := by
  change (ConstantCyclicGroup.component (Spec (.of (PowerSeries K))) n 1 ^ j.toAdd.val) ≫
    ConstantCyclicSectionMap.toScheme (faithfulCompleteMarking K n labels hlabels) = _
  rw [← ConstantCyclicGenerator.component_natCast,
    ConstantCyclicSectionMap.component_toScheme]
  simp only [ZMod.natCast_zmod_val, ofAdd_toAdd]

/-- The original pinched labels retain both coefficient pullback and the corrected group map. -/
theorem completePinchedBoundaryMarking_original (j : Multiplicative (ZMod n)) :
    completePinchedBoundaryMarking K n labels hlabels j =
      GroupSectionBaseChange.pullSection (c) (faithfulCompleteMarking K n labels hlabels j) ≫
        (completeClosedCurveIso K).inv.group := by
  change (((H).baseChange (c)).transport (completeClosedCurveIso K).symm).generatorCurveMarking
    _ j = _
  rw [FiniteSubgroup.generatorCurveMarking_transport _ _
    ((completeFiniteGenerator_isCartierGenerator K n labels hlabels).baseChange (H) (c)),
    FiniteSubgroup.generatorCurveMarking_baseChange]
  change GroupSectionBaseChange.pullSection (c)
    ((H).generatorCurveMarking (completeFiniteGenerator_isCartierGenerator K n labels hlabels) j) ≫
      _ = _
  rw [completeFiniteGenerator_marking]
  rfl

/-- Every original cyclic label stays distinct on every nonempty pinched-curve test. -/
theorem completePinchedBoundaryMarking_distinct :
    UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
      completePinchedBoundaryMarking K n labels hlabels (.ofAdd i)) := by
  intro V k hV i j hij
  apply pullCyclicMarking_distinct (E := completeGeneralizedCurve K) (c)
    (faithfulCompleteMarking K n labels hlabels)
    (faithfulCompleteMarking_distinct K n labels hlabels) V k hV
  let _ : Mono (completeClosedCurveIso K).inv.group :=
    inferInstanceAs (Mono (groupIso (completeClosedCurveIso K)).inv)
  apply (cancel_mono (completeClosedCurveIso K).inv.group).mp
  simp only [completePinchedBoundaryMarking_original] at hij
  simp only [Category.assoc]
  exact hij

end FLT.Mazur.OneGonSmoothing
