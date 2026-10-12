/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationRelation
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer

/-!
# The full slice coequalizes its represented normalization relation

The global retraction supplies both splittings explicitly. Hence the full slice
is the categorical quotient of this relation in schemes, with an explicit
descent formula. Identifying this relation with the modular relation remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n]

/-- Pair each full parameter with its actual normalized full parameter. -/
def cyclicNormalizationRelationSection :
    (cyclicAuxiliaryScheme n).left ⟶ cyclicNormalizationRelation n :=
  pullback.lift (cyclicNormalizationMap n) (𝟙 _)
    ((cyclicNormalizationSliceMap_idempotent n).trans (Category.id_comp _).symm)

/-- The first parameter of the splitting is its full normalization. -/
@[reassoc] theorem cyclicNormalizationRelationSection_first :
    cyclicNormalizationRelationSection n ≫ cyclicNormalizationRelationFirst n =
      cyclicNormalizationMap n :=
  pullback.lift_fst _ _ _

/-- The second parameter of the splitting is the original full parameter. -/
@[reassoc] theorem cyclicNormalizationRelationSection_second :
    cyclicNormalizationRelationSection n ≫ cyclicNormalizationRelationSecond n = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The full slice is a split coequalizer of its actual represented normalization relation. -/
def cyclicNormalizationSplitCoequalizer :
    IsSplitCoequalizer (cyclicNormalizationRelationFirst n)
      (cyclicNormalizationRelationSecond n) (cyclicNormalizationSliceMap n) where
  rightSection := cyclicNormalizedSliceInclusion n
  leftSection := cyclicNormalizationRelationSection n
  condition := cyclicNormalizationRelation_condition n
  rightSection_π := cyclicNormalizationSliceMap_retraction n
  leftSection_bottom := cyclicNormalizationRelationSection_second n
  leftSection_top := (cyclicNormalizationRelationSection_first n).trans
    (cyclicNormalizationSliceMap_inclusion n).symm

/-- The represented normalization relation has the full slice as its categorical quotient. -/
def cyclicNormalizationRelationIsColimit :
    IsColimit (cyclicNormalizationSplitCoequalizer n).asCofork :=
  (cyclicNormalizationSplitCoequalizer n).isCoequalizer

/-- A relation-invariant map is fixed by full normalization. -/
theorem cyclicNormalizationMap_invariant {Y : Scheme}
    (f : (cyclicAuxiliaryScheme n).left ⟶ Y)
    (h : cyclicNormalizationRelationFirst n ≫ f =
      cyclicNormalizationRelationSecond n ≫ f) :
    cyclicNormalizationMap n ≫ f = f := by
  have he := congrArg (fun k ↦ cyclicNormalizationRelationSection n ≫ k) h
  simpa only [← Category.assoc, cyclicNormalizationRelationSection_first,
    cyclicNormalizationRelationSection_second, Category.id_comp] using he

/-- The descended map is restriction to the original full closed slice. -/
@[reassoc] theorem cyclicNormalization_descend {Y : Scheme}
    (f : (cyclicAuxiliaryScheme n).left ⟶ Y)
    (h : cyclicNormalizationRelationFirst n ≫ f =
      cyclicNormalizationRelationSecond n ≫ f) :
    cyclicNormalizationSliceMap n ≫ (cyclicNormalizedSliceInclusion n ≫ f) = f := by
  rw [← Category.assoc, cyclicNormalizationSliceMap_inclusion]
  exact cyclicNormalizationMap_invariant n f h

/-- The full slice descent is unique as an actual scheme morphism. -/
theorem cyclicNormalization_descend_unique {Y : Scheme}
    (f : (cyclicAuxiliaryScheme n).left ⟶ Y) (g : cyclicNormalizedSlice n ⟶ Y)
    (h : cyclicNormalizationSliceMap n ≫ g = f) :
    g = cyclicNormalizedSliceInclusion n ≫ f := by
  rw [← h, ← Category.assoc, cyclicNormalizationSliceMap_retraction, Category.id_comp]

end FLT.Mazur.UniversalWeierstrass
