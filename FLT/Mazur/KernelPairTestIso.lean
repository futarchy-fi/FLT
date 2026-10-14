/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Comparing complete kernel pairs through all test morphisms

Equality of the two kernel predicates constructs an isomorphism preserving
both projections. This works in any category with the required pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace FLT.Mazur.KernelPairTestIso
variable {C : Type u} [Category.{v} C] {A B D : C} (f : A ⟶ B) (g : A ⟶ D)
  [HasPullback f f] [HasPullback g g]
  (h : ∀ {Z : C} (x y : Z ⟶ A), x ≫ f = y ≫ f ↔ x ≫ g = y ≫ g)

/-- An actual isomorphism of full kernel pairs, constructed from both universal predicates. -/
def iso : pullback f f ≅ pullback g g where
  hom := pullback.lift (pullback.fst f f) (pullback.snd f f) ((h _ _).mp pullback.condition)
  inv := pullback.lift (pullback.fst g g) (pullback.snd g g) ((h _ _).mpr pullback.condition)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- The first coordinate is the original kernel projection. -/
@[reassoc]
theorem hom_fst : (iso f g h).hom ≫ pullback.fst g g = pullback.fst f f :=
  pullback.lift_fst _ _ _

/-- The independent second coordinate is preserved as well. -/
@[reassoc]
theorem hom_snd : (iso f g h).hom ≫ pullback.snd g g = pullback.snd f f :=
  pullback.lift_snd _ _ _

end FLT.Mazur.KernelPairTestIso
