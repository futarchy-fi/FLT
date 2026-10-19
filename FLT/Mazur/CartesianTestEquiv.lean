/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Test morphisms into a specified cartesian square

Fixing the first projection identifies tests of the actual pullback object
with tests of the second object over the corresponding composite base map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur
universe v u
variable {C : Type u} [Category.{v} C]

/-- A specified pullback square classifies tests over a fixed first projection. -/
def cartesianTestEquiv {P X Y Z T : C} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) (a : T ⟶ X) :
    {k : T ⟶ P // k ≫ p = a} ≃ {k : T ⟶ Y // k ≫ g = a ≫ f} where
  toFun k := ⟨k.val ≫ q, by rw [Category.assoc, ← h.w, ← Category.assoc, k.property]⟩
  invFun k := ⟨h.lift a k.val k.property.symm, h.lift_fst _ _ _⟩
  left_inv k := by
    apply Subtype.ext
    apply h.hom_ext
    · exact (h.lift_fst _ _ _).trans k.property.symm
    · exact h.lift_snd _ _ _
  right_inv k := Subtype.ext (h.lift_snd _ _ _)

/-- The classification map retains the prescribed actual second projection. -/
theorem cartesianTestEquiv_apply {P X Y Z T : C} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) (a : T ⟶ X)
    (k : {k : T ⟶ P // k ≫ p = a}) :
    (cartesianTestEquiv h a k).val = k.val ≫ q := rfl

end FLT.Mazur
