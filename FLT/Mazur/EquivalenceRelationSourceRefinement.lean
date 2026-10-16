/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSourceRestriction

/-!
# Compatibility of original relations under independent source refinements

Refining either source induces a canonical morphism of the entire restricted
relations. Identity and composition laws hold exactly. The original normalized
arrow and its original relation coordinate are retained as scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  {I : Type} [Fintype I] {o : I} {U V U' V' : Scheme.{0}}
  (j : U ⟶ source p q I o) (k : V ⟶ source p q I o)
  (j' : U' ⟶ source p q I o) (k' : V' ⟶ source p q I o)
  (a : U' ⟶ U) (b : V' ⟶ V) (ha : a ≫ j = j') (hb : b ≫ k = k')

/-- Refine both source maps independently, without restricting the relation's arrows. -/
def refine : relation j' k' ⟶ relation j k :=
  lift j k (fst j' k' ≫ a) (snd j' k' ≫ b) (arrow j' k')
    (by rw [Category.assoc, ← Category.assoc a, ha]; exact arrow_first j' k')
    (by rw [Category.assoc, ← Category.assoc b, hb]; exact arrow_second j' k')

/-- Refinement retains the first source lift. -/
@[reassoc] theorem refine_fst : refine j k j' k' a b ha hb ≫ fst j k = fst j' k' ≫ a :=
  lift_fst _ _ _ _ _ _ _

/-- Refinement retains the independent second source lift. -/
@[reassoc] theorem refine_snd : refine j k j' k' a b ha hb ≫ snd j k = snd j' k' ≫ b :=
  lift_snd _ _ _ _ _ _ _

/-- Refinement retains the unchanged original relation coordinate. -/
@[reassoc] theorem refine_arrow : refine j k j' k' a b ha hb ≫ arrow j k = arrow j' k' :=
  lift_arrow _ _ _ _ _ _ _

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Both independent endpoints and the entire original normalized arrow commute with refinement. -/
@[reassoc] theorem refine_original :
    refine j k j' k' a b ha hb ≫ original j k = original j' k' := by
  apply relation_hom_ext p q I o e
  · rw [Category.assoc, original_first, ← Category.assoc, refine_fst,
      Category.assoc, ha, original_first]
  · rw [Category.assoc, original_second, ← Category.assoc, refine_snd,
      Category.assoc, hb, original_second]

include e in
/-- The identity source refinements induce the identity on the whole original relation. -/
theorem refine_id : refine j k j k (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) =
    𝟙 (relation j k) := by
  apply hom_ext j k e
  · rw [refine_fst, Category.comp_id, Category.id_comp]
  · rw [refine_snd, Category.comp_id, Category.id_comp]

include e in
/-- Successive independent source refinements compose on the entire original relation. -/
theorem refine_comp {U'' V'' : Scheme.{0}}
    (j'' : U'' ⟶ source p q I o) (k'' : V'' ⟶ source p q I o)
    (a' : U'' ⟶ U') (b' : V'' ⟶ V') (ha' : a' ≫ j' = j'') (hb' : b' ≫ k' = k'') :
    refine j' k' j'' k'' a' b' ha' hb' ≫ refine j k j' k' a b ha hb =
      refine j k j'' k'' (a' ≫ a) (b' ≫ b)
        (by rw [Category.assoc, ha, ha']) (by rw [Category.assoc, hb, hb']) := by
  apply hom_ext j k e
  · rw [Category.assoc, refine_fst, ← Category.assoc, refine_fst,
      Category.assoc, refine_fst]
  · rw [Category.assoc, refine_snd, ← Category.assoc, refine_snd,
      Category.assoc, refine_snd]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
