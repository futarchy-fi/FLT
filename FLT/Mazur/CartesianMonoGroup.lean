/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianMonoMonoid
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Restricting group operations along a monomorphism

An inverse and multiplication preserving an ambient commutative group give
a commutative group on the subobject, with every identity proved by cancellation.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace FLT.Mazur.CartesianMonoGroup

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
  {X Y : C} [GrpObj Y] (i : X ⟶ Y) [Mono i]
  (o : 𝟙_ C ⟶ X) (m : X ⊗ X ⟶ X) (n : X ⟶ X)
  (ho : o ≫ i = η[Y]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[Y])
  (hn : n ≫ i = i ≫ ι[Y])

/-- The restricted operations give an actual group object. -/
@[instance_reducible] def grpObj : GrpObj X where
  __ := CartesianMonoMonoid.monObj i o m ho hm
  inv := n
  left_inv := by
    change lift n (𝟙 X) ≫ m = toUnit X ≫ o
    apply (cancel_mono i).mp
    rw [Category.assoc, CartesianMonoMonoid.pair_map i m hm, hn,
      Category.id_comp, Category.assoc, ho]
    simp
  right_inv := by
    change lift (𝟙 X) n ≫ m = toUnit X ≫ o
    apply (cancel_mono i).mp
    rw [Category.assoc, CartesianMonoMonoid.pair_map i m hm, hn,
      Category.id_comp, Category.assoc, ho]
    simp

/-- Commutativity of the actual restricted multiplication follows from naturality. -/
@[instance_reducible] def commGrpObj [BraidedCategory C] [IsCommMonObj Y] : CommGrpObj X where
  __ := grpObj i o m n ho hm hn
  mul_comm := by
    apply (cancel_mono i).mp
    change ((β_ X X).hom ≫ m) ≫ i = m ≫ i
    rw [Category.assoc, hm, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

end FLT.Mazur.CartesianMonoGroup
