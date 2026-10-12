/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentCyclicAuxiliaryScheme
public import FLT.Mazur.UniversalWeierstrassFullNormalizationParameter
public import FLT.Mazur.AuxiliaryDistinctSectionParameter

/-!
# Original source sections for independent cyclic parameters

Realize the cyclic parameter on the full original auxiliary source group.
Faithfulness of this factor alone proves universal distinctness, with no
condition on intersections with the auxiliary four-torsion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (independentCyclicAuxiliaryScheme n).left)

/-- The original auxiliary point associated with the independent pair. -/
def independentCyclicAuxiliaryPoint : T ⟶ levelFour.left :=
  f ≫ (independentCyclicAuxiliary n).left

/-- The cyclic parameter lies over the exact same original coefficient map. -/
def independentCyclicGroupPoint :
    (Over.map (independentCyclicAuxiliaryPoint n f ≫ levelFour.hom)).obj
      (𝟙_ (Over T)) ⟶ faithfulScheme universalGroup (Multiplicative (ZMod n)) :=
  Over.homMk (f ≫ (independentCyclicParameter n).left) (by
    change (f ≫ (independentCyclicParameter n).left) ≫ _ =
      𝟙 T ≫ (independentCyclicAuxiliaryPoint n f ≫ levelFour.hom)
    rw [Category.id_comp, Category.assoc, (independentCyclicParameter n).w]
    rw [independentCyclicAuxiliaryPoint, Category.assoc, (independentCyclicAuxiliary n).w])

/-- The actual cyclic parameter on the original source group. -/
def independentCyclicOriginalParameter : 𝟙_ (Over T) ⟶
    faithfulScheme (auxiliarySchemeGroup (independentCyclicAuxiliaryPoint n f)).X
      (Multiplicative (ZMod n)) :=
  auxiliarySchemeFullOriginalParameter (independentCyclicAuxiliaryPoint n f)
    (Multiplicative (ZMod n)) (independentCyclicGroupPoint n f)

/-- All cyclic source sections, without any additional auxiliary labels. -/
def independentCyclicSourceMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over T) ⟶ (auxiliarySchemeGroup (independentCyclicAuxiliaryPoint n f)).X) :=
  markingOf _ _ (independentCyclicOriginalParameter n f ≫ faithfulInclusion _ _)

/-- Independent cyclic sections stay distinct on every nonempty test scheme. -/
theorem independentCyclicSourceMarking_distinct :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ independentCyclicSourceMarking n f (.ofAdd i)) := by
  intro V g hV i j hij
  let _ := hV
  have hh := faithful_marking_injective _ _ (g ≫ independentCyclicOriginalParameter n f)
  apply congrArg Multiplicative.toAdd (hh (a₁ := Multiplicative.ofAdd i)
    (a₂ := Multiplicative.ofAdd j) ?_)
  change (g ≫ independentCyclicOriginalParameter n f) ≫ faithfulInclusion _ _ ≫
    value _ _ (Multiplicative.ofAdd i) =
      (g ≫ independentCyclicOriginalParameter n f) ≫ faithfulInclusion _ _ ≫
        value _ _ (Multiplicative.ofAdd j)
  change g ≫ ((independentCyclicOriginalParameter n f ≫ faithfulInclusion _ _) ≫
    value _ _ (Multiplicative.ofAdd i)) =
      g ≫ ((independentCyclicOriginalParameter n f ≫ faithfulInclusion _ _) ≫
        value _ _ (Multiplicative.ofAdd j)) at hij
  simpa only [Category.assoc] using hij

/-- Projection retains the actual original universal cyclic section at every label. -/
@[reassoc] theorem independentCyclicSourceMarking_fst (b : Multiplicative (ZMod n)) :
    (independentCyclicSourceMarking n f b).left ≫ pullback.fst universalGroup.hom
      (independentCyclicAuxiliaryPoint n f ≫ levelFour.hom) =
        f ≫ (independentCyclicParameter n ≫ faithfulInclusion universalGroup
          (Multiplicative (ZMod n)) ≫ value universalGroup (Multiplicative (ZMod n)) b).left := by
  have hv := cartesianGroupParameter_value
    (independentCyclicAuxiliaryPoint n f ≫ levelFour.hom)
    (integralCurveGroup smoothEquation smoothEquation_discriminant)
    (auxiliarySchemeGroup (independentCyclicAuxiliaryPoint n f)) (Iso.refl _)
    (Multiplicative (ZMod n)) (independentCyclicGroupPoint n f) b
  change independentCyclicSourceMarking n f b = _ at hv
  rw [hv]
  have h := cartesianGroupMarking_projection
    (independentCyclicAuxiliaryPoint n f ≫ levelFour.hom)
    (integralCurveGroup smoothEquation smoothEquation_discriminant)
    (auxiliarySchemeGroup (independentCyclicAuxiliaryPoint n f)) (Iso.refl _)
    (Multiplicative (ZMod n)) (independentCyclicGroupPoint n f) b
  change _ ≫ 𝟙 _ ≫ pullback.fst universalGroup.hom
    (independentCyclicAuxiliaryPoint n f ≫ levelFour.hom) = _ at h
  rw [Category.id_comp] at h
  refine h.trans ?_
  change (f ≫ (independentCyclicParameter n).left) ≫
    (faithfulInclusion universalGroup (Multiplicative (ZMod n)) ≫
      value universalGroup (Multiplicative (ZMod n)) b).left = _
  simp only [Over.comp_left, Category.assoc]

end FLT.Mazur.UniversalWeierstrass
