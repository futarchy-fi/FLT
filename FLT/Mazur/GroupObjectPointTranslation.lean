/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Translation and normalization of group-object automorphisms

A point defines an actual translation isomorphism. Subtracting the image of
identity normalizes any underlying automorphism to one fixing identity.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.GroupObjectPointTranslation
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G]

/-- Left translation by an actual point of the group object. -/
def translation (p : 𝟙_ C ⟶ G) : G ⟶ G := (toUnit G ≫ p) * 𝟙 G

/-- Translation on every test object is multiplication by the pulled-back point. -/
@[reassoc] theorem comp_translation {X : C} (f : X ⟶ G) (p : 𝟙_ C ⟶ G) :
    f ≫ translation p = (toUnit X ≫ p) * f := by
  simp only [translation, MonObj.comp_mul, ← Category.assoc,
    comp_toUnit, Category.comp_id]

/-- Successive translations retain the original multiplication order. -/
theorem translation_comp (p q : 𝟙_ C ⟶ G) :
    translation p ≫ translation q = translation (q * p) := by
  rw [comp_translation]
  simp only [translation, MonObj.comp_mul, mul_assoc]

/-- The identity point induces the identity morphism. -/
@[simp] theorem translation_one : translation (1 : 𝟙_ C ⟶ G) = 𝟙 G := by
  simp only [translation, MonObj.comp_one, one_mul]

/-- Inversion of the actual point supplies the inverse translation. -/
def translationIso (p : 𝟙_ C ⟶ G) : G ≅ G where
  hom := translation p
  inv := translation p⁻¹
  hom_inv_id := by rw [translation_comp, inv_mul_cancel, translation_one]
  inv_hom_id := by rw [translation_comp, mul_inv_cancel, translation_one]

/-- The identity point goes to the original point under its translation. -/
@[simp] theorem one_translation (p : 𝟙_ C ⟶ G) :
    (1 : 𝟙_ C ⟶ G) ≫ translation p = p := by
  rw [comp_translation]
  simp only [toUnit_unit, Category.id_comp, mul_one]

/-- Normalize a given automorphism by its actual image of the identity point. -/
def normalizedIso (e : G ≅ G) : G ≅ G :=
  e ≪≫ translationIso (((1 : 𝟙_ C ⟶ G) ≫ e.hom)⁻¹)

/-- Normalization on every test object subtracts the original identity image. -/
@[reassoc] theorem comp_normalizedIso {X : C} (f : X ⟶ G) (e : G ≅ G) :
    f ≫ (normalizedIso e).hom =
      (toUnit X ≫ ((1 : 𝟙_ C ⟶ G) ≫ e.hom)⁻¹) * (f ≫ e.hom) := by
  dsimp only [normalizedIso, Iso.trans_hom, translationIso]
  rw [← Category.assoc, comp_translation]

/-- Normalization fixes the original identity as an equality of morphisms. -/
theorem normalizedIso_one (e : G ≅ G) :
    (1 : 𝟙_ C ⟶ G) ≫ (normalizedIso e).hom = 1 := by
  dsimp only [normalizedIso, Iso.trans_hom, translationIso]
  rw [← Category.assoc, comp_translation]
  simp only [toUnit_unit, Category.id_comp, inv_mul_cancel]

/-- Reattaching the actual identity image recovers the original automorphism. -/
theorem normalizedIso_translation (e : G ≅ G) :
    (normalizedIso e).hom ≫ translation ((1 : 𝟙_ C ⟶ G) ≫ e.hom) = e.hom := by
  dsimp only [normalizedIso, Iso.trans_hom, translationIso]
  rw [Category.assoc, translation_comp, mul_inv_cancel, translation_one, Category.comp_id]

/-- Translation identification is equivalent to triviality of the normalized automorphism. -/
theorem eq_translation_iff (e : G ≅ G) :
    e.hom = translation ((1 : 𝟙_ C ⟶ G) ≫ e.hom) ↔ (normalizedIso e).hom = 𝟙 G := by
  constructor
  · intro he
    change e.hom ≫ translation (((1 : 𝟙_ C ⟶ G) ≫ e.hom)⁻¹) = 𝟙 G
    conv_lhs => lhs; rw [he]
    rw [translation_comp, inv_mul_cancel, translation_one]
  · intro he
    have hr := normalizedIso_translation e
    rw [he, Category.id_comp] at hr
    exact hr.symm

end FLT.Mazur.GroupObjectPointTranslation
