/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# From represented membership to an actual presheaf pullback

If membership of restrictions is represented by a monomorphism of tests,
the corresponding square of presheaves is cartesian. Universe lifting is
explicit, so this applies to the actual relative Picard sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace FLT.Mazur.PicardOpenRepresentation
universe u v w
variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type (max v w)}
  (G : Subfunctor F) {A B : C} (j : B ⟶ A) [Mono j] (s : F.obj (op A))
  (h : ∀ {U : C} (b : U ⟶ A), F.map b.op s ∈ G.obj (op U) ↔
    ∃! k : U ⟶ B, k ≫ j = b)

/-- The represented test maps to the subfunctor by restricting the original section. -/
def lift : uliftYoneda.{w}.obj B ⟶ G.toFunctor where
  app U := ↾fun k ↦ ⟨F.map (k.down ≫ j).op s,
    (h _).mpr ⟨k.down, rfl, fun l hl ↦ (cancel_mono j).mp hl⟩⟩
  naturality {U V} g := by
    apply ConcreteCategory.hom_ext
    intro k
    apply Subtype.ext
    change F.map ((g.unop ≫ k.down) ≫ j).op s = F.map g (F.map (k.down ≫ j).op s)
    simp only [Category.assoc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      Quiver.Hom.op_unop]

/-- The representing test square is an actual pullback in the presheaf category. -/
theorem isPullback : IsPullback (lift G j s h) (uliftYoneda.{w}.map j)
    G.ι (uliftYonedaEquiv.symm s) := by
  apply IsPullback.of_forall_isPullback_app
  intro U
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro k l hkl
    apply ULift.ext
    apply (cancel_mono j).mp
    exact congrArg ULift.down hkl.2
  · intro c b hcb
    change c.val = F.map b.down.op s at hcb
    obtain ⟨k, hk, _⟩ := (h b.down).mp (hcb ▸ c.property)
    refine ⟨ULift.up k, ?_, ?_⟩
    · apply Subtype.ext
      change F.map (k ≫ j).op s = c.val
      rw [hk, hcb]
    · exact ULift.ext hk

end FLT.Mazur.PicardOpenRepresentation
