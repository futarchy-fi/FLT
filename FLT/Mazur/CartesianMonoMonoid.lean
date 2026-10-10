/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Restricting monoid operations along a monomorphism

Operations which preserve a monomorphism into a monoid satisfy its laws.
The hypotheses concern the actual unit and multiplication maps only.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace FLT.Mazur.CartesianMonoMonoid

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
  {X Y : C} [MonObj Y] (i : X ⟶ Y) [Mono i]
  (o : 𝟙_ C ⟶ X) (m : X ⊗ X ⟶ X)
  (ho : o ≫ i = η[Y]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[Y])

include hm in
omit [Mono i] in
/-- The restricted operation on arbitrary pairs agrees with the ambient operation. -/
@[reassoc] theorem pair_map {T : C} (f g : T ⟶ X) :
    lift f g ≫ m ≫ i = lift (f ≫ i) (g ≫ i) ≫ μ[Y] := by
  rw [hm, ← Category.assoc]
  congr 1
  ext <;> simp

include ho hm in
/-- The restricted operation has a left identity on every family of points. -/
theorem pair_one_left {T : C} (f : T ⟶ 𝟙_ C) (g : T ⟶ X) :
    lift (f ≫ o) g ≫ m = g := by
  apply (cancel_mono i).mp
  rw [Category.assoc, pair_map i m hm, Category.assoc, ho]
  exact MonObj.lift_comp_one_left f (g ≫ i)

include ho hm in
/-- The restricted operation has a right identity on every family of points. -/
theorem pair_one_right {T : C} (f : T ⟶ X) (g : T ⟶ 𝟙_ C) :
    lift f (g ≫ o) ≫ m = f := by
  apply (cancel_mono i).mp
  rw [Category.assoc, pair_map i m hm, Category.assoc, ho]
  exact MonObj.lift_comp_one_right (f ≫ i) g

include hm in
/-- Associativity descends along the monomorphism for every triple of points. -/
theorem pair_assoc {T : C} (f g h : T ⟶ X) :
    lift (lift f g ≫ m) h ≫ m = lift f (lift g h ≫ m) ≫ m := by
  apply (cancel_mono i).mp
  simp only [Category.assoc, pair_map i m hm]
  exact MonObj.lift_lift_assoc (f ≫ i) (g ≫ i) (h ≫ i)

/-- The actual restricted maps give a monoid object; all laws are derived. -/
@[instance_reducible] def monObj : MonObj X where
  one := o
  mul := m
  one_mul := by
    calc
      _ = lift (fst _ _ ≫ o) (snd _ _) ≫ m := by congr 1; ext <;> simp
      _ = snd _ _ := pair_one_left i o m ho hm _ _
      _ = (λ_ X).hom := (leftUnitor_hom X).symm
  mul_one := by
    calc
      _ = lift (fst _ _) (snd _ _ ≫ o) ≫ m := by congr 1; ext <;> simp
      _ = fst _ _ := pair_one_right i o m ho hm _ _
      _ = (ρ_ X).hom := (rightUnitor_hom X).symm
  mul_assoc := by
    have h := pair_assoc i m hm (fst (X ⊗ X) X ≫ fst X X)
      (fst (X ⊗ X) X ≫ snd X X) (snd (X ⊗ X) X)
    convert h using 1
    · congr 1
      ext <;> simp
    · rw [← Category.assoc]
      congr 1
      apply hom_ext
      · simp
      · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
        rw [← Category.assoc]
        congr 1
        ext <;> simp

end FLT.Mazur.CartesianMonoMonoid
