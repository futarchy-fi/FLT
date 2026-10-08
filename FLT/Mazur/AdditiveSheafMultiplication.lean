/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Multiplication on a specified additive sheaf

An additive comparison with a ring sheaf transports its product and unit
without replacing the sections or their existing additive group structure.
The operations commute with the original restriction maps.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace FLT.Mazur.AdditiveSheafMultiplication

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (A : Sheaf J AddCommGrpCat.{max u v}) (R : Sheaf J CommRingCat.{max u v})

/-- The additive forgetful functor for a commutative ring sheaf. -/
abbrev forgetAdd : CommRingCat.{w} ⥤ AddCommGrpCat.{w} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

variable (e : A ≅ (sheafCompose J forgetAdd.{max u v}).obj R)

/-- The section comparison, with its ring-valued target made explicit. -/
def sectionEquiv (U : Cᵒᵖ) : A.obj.obj U ≃+ R.obj.obj U where
  toFun := e.hom.hom.app U
  invFun := e.inv.hom.app U
  left_inv := (((sheafToPresheaf J AddCommGrpCat).mapIso e).app U).hom_inv_id_apply
  right_inv := (((sheafToPresheaf J AddCommGrpCat).mapIso e).app U).inv_hom_id_apply
  map_add' := (e.hom.hom.app U).hom.map_add

/-- The section comparison commutes with restriction. -/
lemma map_restrict {U V : Cᵒᵖ} (i : U ⟶ V) (s : A.obj.obj U) :
    sectionEquiv A R e V (A.obj.map i s) = R.obj.map i (sectionEquiv A R e U s) :=
  ConcreteCategory.congr_hom (e.hom.hom.naturality i) s

/-- The original additive sections, with the ring sheaf's product transported to them. -/
def mul (U : Cᵒᵖ) (s t : A.obj.obj U) : A.obj.obj U :=
  (sectionEquiv A R e U).symm (sectionEquiv A R e U s * sectionEquiv A R e U t)

/-- The unit on the original additive sections. -/
def one (U : Cᵒᵖ) : A.obj.obj U := (sectionEquiv A R e U).symm 1

/-- The additive comparison recovers exactly the ring sheaf's product. -/
lemma map_mul (U : Cᵒᵖ) (s t : A.obj.obj U) :
    sectionEquiv A R e U (mul A R e U s t) =
      sectionEquiv A R e U s * sectionEquiv A R e U t := by
  exact (sectionEquiv A R e U).apply_symm_apply _

/-- The additive comparison recovers the original unit. -/
lemma map_one (U : Cᵒᵖ) : sectionEquiv A R e U (one A R e U) = 1 := by
  exact (sectionEquiv A R e U).apply_symm_apply _

/-- Restriction of the transported product is the product of restrictions. -/
lemma restrict_mul {U V : Cᵒᵖ} (i : U ⟶ V) (s t : A.obj.obj U) :
    A.obj.map i (mul A R e U s t) =
      mul A R e V (A.obj.map i s) (A.obj.map i t) := by
  apply (sectionEquiv A R e V).injective
  rw [map_restrict, map_mul, map_mul, _root_.map_mul, map_restrict, map_restrict]

/-- Restriction preserves the transported unit. -/
lemma restrict_one {U V : Cᵒᵖ} (i : U ⟶ V) :
    A.obj.map i (one A R e U) = one A R e V := by
  apply (sectionEquiv A R e V).injective
  rw [map_restrict, map_one, map_one, _root_.map_one]

/-- Associativity holds on the unchanged additive section groups. -/
lemma mul_assoc (U : Cᵒᵖ) (s t r : A.obj.obj U) :
    mul A R e U (mul A R e U s t) r = mul A R e U s (mul A R e U t r) := by
  apply (sectionEquiv A R e U).injective
  simp only [map_mul, _root_.mul_assoc]

/-- The transported product is commutative. -/
lemma mul_comm (U : Cᵒᵖ) (s t : A.obj.obj U) :
    mul A R e U s t = mul A R e U t s := by
  apply (sectionEquiv A R e U).injective
  simp only [map_mul, _root_.mul_comm]

/-- The transported unit is a left identity. -/
lemma one_mul (U : Cᵒᵖ) (s : A.obj.obj U) : mul A R e U (one A R e U) s = s := by
  apply (sectionEquiv A R e U).injective
  simp only [map_mul, map_one, _root_.one_mul]

/-- Multiplication distributes over the existing addition. -/
lemma mul_add (U : Cᵒᵖ) (s t r : A.obj.obj U) :
    mul A R e U s (t + r) = mul A R e U s t + mul A R e U s r := by
  apply (sectionEquiv A R e U).injective
  simp only [map_mul, _root_.map_add, _root_.mul_add]

end FLT.Mazur.AdditiveSheafMultiplication
