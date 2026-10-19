/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Products over a monomorphic coefficient base

The product of two schemes over a smaller base is unchanged after composing
both structure maps with a monomorphism. Both original projections are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.MonoBaseProductComparison

universe u v
variable {C : Type u} [Category.{v} C] {X Y S T : C}
  (f : X ⟶ S) (g : Y ⟶ S) (b : S ⟶ T) [Mono b]
  [HasPullback f g] [HasPullback (f ≫ b) (g ≫ b)]

/-- Forgetting a monomorphic coefficient base does not change the actual product. -/
def iso : pullback (f ≫ b) (g ≫ b) ≅ pullback f g where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    apply (cancel_mono b).mp
    simpa only [Category.assoc] using (pullback.condition (f := f ≫ b) (g := g ≫ b)))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    simpa only [Category.assoc] using congrArg (· ≫ b) (pullback.condition (f := f) (g := g)))
  hom_inv_id := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst,
      pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst,
      pullback.lift_snd, Category.id_comp]

/-- The first original projection is unchanged. -/
@[reassoc (attr := simp)] theorem iso_hom_fst :
    (iso f g b).hom ≫ pullback.fst f g = pullback.fst _ _ := pullback.lift_fst _ _ _

/-- The second original projection is unchanged. -/
@[reassoc (attr := simp)] theorem iso_hom_snd :
    (iso f g b).hom ≫ pullback.snd f g = pullback.snd _ _ := pullback.lift_snd _ _ _

/-- The inverse comparison also retains the first original projection. -/
@[reassoc (attr := simp)] theorem iso_inv_fst :
    (iso f g b).inv ≫ pullback.fst _ _ = pullback.fst f g := pullback.lift_fst _ _ _

/-- The inverse comparison also retains the second original projection. -/
@[reassoc (attr := simp)] theorem iso_inv_snd :
    (iso f g b).inv ≫ pullback.snd _ _ = pullback.snd f g := pullback.lift_snd _ _ _

end FLT.Mazur.MonoBaseProductComparison
