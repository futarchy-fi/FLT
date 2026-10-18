/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFaithfulCompleteDivisor
public import FLT.Mazur.SectionCartesianKernel

/-!
# Original closed-fiber comparison for the complete cyclic subgroup

The original torus labels determine the closed subgroup map. Each complete
component specializes to that map, and the entire subgroup ideal pulls back
to its original closed ideal, with all scheme structure retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The full-curve closed subgroup associated with the original faithful torus labels. -/
def faithfulClosedCurveMap : ConstantCyclicGroup.model (Spec (.of K)) n ⟶
    (Over.pullback (c)).obj (family (t)) :=
  relativeCyclicCurveMap (t) n (c) (closedCyclicParameter K n labels hlabels)

/-- Its components are the unchanged original closed smooth sections in the whole curve. -/
@[reassoc] theorem faithfulClosedCurveMap_component (i : ZMod n) :
    ConstantCyclicGroup.component (Spec (.of K)) n i ≫
      faithfulClosedCurveMap K n labels hlabels =
        closedCyclicSections K n labels (.ofAdd i) ≫ relativeTestInclusion (t) (c) := by
  rw [faithfulClosedCurveMap, relativeCyclicCurveMap_component, closedCyclicParameter_sections]

/-- Projection of the whole closed component equals restriction of its original complete label. -/
@[reassoc] theorem faithfulClosedCurveMap_component_fst (i : ZMod n) :
    (ConstantCyclicGroup.component (Spec (.of K)) n i ≫
      faithfulClosedCurveMap K n labels hlabels).left ≫ pullback.fst (family (t)).hom (c) =
        (c) ≫ (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫
          relativeGroupInclusion (t)).left := by
  rw [faithfulClosedCurveMap_component]
  change ((closedCyclicSections K n labels (.ofAdd i)).left ≫
    pullback.lift _ _ _) ≫ _ = _
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
    ← closedCyclicMarking_left]
  have he := congrArg Over.Hom.left
    (faithfulCompleteMarking_reduction K n labels hlabels (.ofAdd i))
  change (c) ≫ _ = _ at he
  rw [← he, Category.assoc]
  rfl

/-- The whole closed subgroup is a closed embedding, including at the nodal fiber. -/
theorem faithfulClosedCurveMap_closed :
    IsClosedImmersion (faithfulClosedCurveMap K n labels hlabels).left :=
  relativeCyclicCurveMap_closed (t) n (c) (closedCyclicParameter K n labels hlabels)

/-- The full original complete subgroup ideal specializes to the original closed subgroup ideal. -/
theorem faithfulCompleteIdeal_closed :
    (faithfulCompleteIdeal K n labels hlabels).comap (pullback.fst (family (t)).hom (c)) =
      (faithfulClosedCurveMap K n labels hlabels).left.ker := by
  let _ := family_proper (t)
  rw [faithfulCompleteIdeal_product]
  have he := section_prod_comap_of_cartesian (IsPullback.of_hasPullback (family (t)).hom (c))
    Finset.univ
    (fun i : ZMod n ↦ (ConstantCyclicGroup.component (Spec (.of K)) n i ≫
      faithfulClosedCurveMap K n labels hlabels).left)
    (fun i : ZMod n ↦ (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫
      relativeGroupInclusion (t)).left)
    (fun i ↦ (ConstantCyclicGroup.component (Spec (.of K)) n i ≫
      faithfulClosedCurveMap K n labels hlabels).w)
    (fun i ↦ (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫
      relativeGroupInclusion (t)).w)
    (faithfulClosedCurveMap_component_fst K n labels hlabels)
  refine he.trans ?_
  change _ = relativeCyclicIdeal (t) n (c) (closedCyclicParameter K n labels hlabels)
  rw [relativeCyclicIdeal_product]
  apply Finset.prod_congr rfl
  intro i _
  rw [faithfulClosedCurveMap_component, closedCyclicParameter_sections]

end FLT.Mazur.OneGonSmoothing
