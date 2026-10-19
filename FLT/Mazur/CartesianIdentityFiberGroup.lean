/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianMonoGroup
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Group operations on an exact Cartesian identity fiber

The pullback of the identity along a group homomorphism carries the restricted
operations on its original carrier. Cancellation proves the group laws.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace FLT.Mazur.CartesianIdentityFiberGroup

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {X G J : C} [CommGrpObj G] [CommGrpObj J]
  (f : G ⟶ J) [IsMonHom f] (i : X ⟶ G) (k : X ⟶ 𝟙_ C)
  (h : IsPullback i k f η[J])

/-- The exact fiber inherits the original identity. -/
def one : 𝟙_ C ⟶ X := h.lift η[G] (𝟙 _) (by simp)

/-- The exact fiber's identity retains the original inclusion. -/
@[reassoc] theorem one_inclusion : one f i k h ≫ i = η[G] := h.lift_fst _ _ _

include h in
/-- Products in the actual identity fiber remain killed by the original homomorphism. -/
theorem multiplication_zero : ((i ⊗ₘ i) ≫ μ[G]) ≫ f = toUnit (X ⊗ X) ≫ η[J] := by
  rw [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h.w]
  rw [← lift_fst_comp_snd_comp]
  simp only [← Category.assoc, MonObj.lift_comp_one_left]
  exact congrArg (· ≫ η[J]) (Subsingleton.elim _ _)

/-- Construct multiplication on the exact original fiber by its universal property. -/
def mul : X ⊗ X ⟶ X :=
  h.lift ((i ⊗ₘ i) ≫ μ[G]) (toUnit _) (multiplication_zero f i k h)

/-- Multiplication retains the original ambient multiplication. -/
@[reassoc] theorem mul_inclusion : mul f i k h ≫ i = (i ⊗ₘ i) ≫ μ[G] := h.lift_fst _ _ _

/-- Construct the inverse on the exact original fiber by its universal property. -/
def inv : X ⟶ X := h.lift (i ≫ ι[G]) k (by
  rw [Category.assoc, GrpObj.inv_hom, ← Category.assoc, h.w, Category.assoc]
  simp)

/-- The inverse retains the original ambient inverse. -/
@[reassoc] theorem inv_inclusion : inv f i k h ≫ i = i ≫ ι[G] := h.lift_fst _ _ _

/-- The exact Cartesian identity fiber is an actual commutative group object. -/
@[instance_reducible] def commGrpObj [Mono i] : CommGrpObj X :=
  CartesianMonoGroup.commGrpObj i (one f i k h) (mul f i k h) (inv f i k h)
    (one_inclusion f i k h) (mul_inclusion f i k h) (inv_inclusion f i k h)

/-- The original inclusion preserves the constructed group operations. -/
theorem inclusion_isMonHom [Mono i] :
    let _ := commGrpObj f i k h
    IsMonHom i := by
  let _ := commGrpObj f i k h
  exact ⟨one_inclusion f i k h, mul_inclusion f i k h⟩

end FLT.Mazur.CartesianIdentityFiberGroup
