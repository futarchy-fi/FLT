/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCyclicParameterSections

/-!
# The lifted cyclic subgroup on the original complete curve

The actual complete labels define a group-scheme inclusion. Universal
distinctness follows from the faithful parameter, and properness closes
the subgroup in the whole original cubic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))

/-- Complete labels are distinct after every nonempty scheme test of the original base. -/
theorem faithfulCompleteMarking_distinct :
    UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
      faithfulCompleteMarking K n labels hlabels (.ofAdd i)) := by
  intro V k hV i j hij
  apply relativeCyclicMarking_distinct (t) n (𝟙 _)
    (faithfulCompleteParameter K n labels hlabels) V k hV
  apply Over.OverMorphism.ext
  apply (cancel_mono (pullback.fst (relativeGroup (t)).X.hom (𝟙 S))).mp
  simpa only [Over.comp_left, Category.assoc, faithfulCompleteSections_fst] using
    congrArg Over.Hom.left hij

/-- The full constant cyclic group maps to the original complete smooth group. -/
def faithfulCompleteInclusion : ConstantCyclicGroup.model S n ⟶ (relativeGroup (t)).X :=
  ConstantCyclicSectionMap.toScheme (faithfulCompleteMarking K n labels hlabels)

/-- This original inclusion preserves the group operations. -/
instance faithfulCompleteInclusion_isMonHom :
    IsMonHom (faithfulCompleteInclusion K n labels hlabels) :=
  ConstantCyclicSectionMap.toScheme_isMonHom _

/-- The complete subgroup embeds as a closed subgroup of the actual smooth group. -/
instance faithfulCompleteInclusion_closed :
    IsClosedImmersion (faithfulCompleteInclusion K n labels hlabels).left :=
  ConstantCyclicRelativeClosed.toScheme_closed _
    (faithfulCompleteMarking_distinct K n labels hlabels)

/-- The subgroup retains its embedding in the original entire complete cubic. -/
def faithfulCompleteCurveMap : ConstantCyclicGroup.model S n ⟶ family (t) :=
  faithfulCompleteInclusion K n labels hlabels ≫ relativeGroupInclusion (t)

/-- Every full-curve component is the corresponding constructed original label. -/
@[reassoc] theorem faithfulCompleteCurveMap_component (i : ZMod n) :
    ConstantCyclicGroup.component S n i ≫ faithfulCompleteCurveMap K n labels hlabels =
      faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫ relativeGroupInclusion (t) :=
  ConstantCyclicSectionMap.component_toScheme_assoc _ i _

/-- The full-curve sections remain universally distinct. -/
theorem faithfulCompleteCurveMap_distinct :
    UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
      ConstantCyclicGroup.component S n i ≫ faithfulCompleteCurveMap K n labels hlabels) := by
  intro V k hV i j hij
  apply faithfulCompleteMarking_distinct K n labels hlabels V k hV
  have : Mono (relativeGroupInclusion (t)) := Over.mono_of_mono_left _
  apply (cancel_mono (relativeGroupInclusion (t))).mp
  simpa only [faithfulCompleteCurveMap_component, Category.assoc] using hij

/-- The lifted subgroup is closed in the entire original proper curve. -/
theorem faithfulCompleteCurveMap_closed :
    IsClosedImmersion (faithfulCompleteCurveMap K n labels hlabels).left := by
  let _ := family_proper (t)
  exact ConstantCyclicRelativeClosed.closed _
    (faithfulCompleteCurveMap_distinct K n labels hlabels)

end FLT.Mazur.OneGonSmoothing
