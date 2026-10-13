/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Translation on an object acted on by a group object

Every point of the group, including a varying section over a scheme base,
acts by an actual automorphism on the entire acted-on object.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.GroupActionPointTranslation
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G X : C} [GrpObj G] [ModObj G X]

/-- Specialization of the action at an arbitrary group point. -/
def translation (p : 𝟙_ C ⟶ G) : X ⟶ X := (toUnit X ≫ p) • 𝟙 X

/-- Every test morphism sees the action of the pulled-back group point. -/
@[reassoc] theorem comp_translation {Y : C} (f : Y ⟶ X) (p : 𝟙_ C ⟶ G) :
    f ≫ translation p = (toUnit Y ≫ p) • f := by
  simp only [translation, ModObj.comp_smul, ← Category.assoc, comp_toUnit, Category.comp_id]

/-- Successive translations retain the action's multiplication order. -/
theorem translation_comp (p q : 𝟙_ C ⟶ G) :
    translation (X := X) p ≫ translation q = translation (q * p) := by
  rw [comp_translation]
  simp only [translation, MonObj.comp_mul, mul_smul]

/-- The identity group point acts identically on the entire object. -/
@[simp] theorem translation_one : translation (X := X) (1 : 𝟙_ C ⟶ G) = 𝟙 X := by
  simp only [translation, MonObj.comp_one, one_smul]

/-- Inverting the parameter gives an inverse on the whole acted-on object. -/
def translationIso (p : 𝟙_ C ⟶ G) : X ≅ X where
  hom := translation p
  inv := translation p⁻¹
  hom_inv_id := by rw [translation_comp, inv_mul_cancel, translation_one]
  inv_hom_id := by rw [translation_comp, mul_inv_cancel, translation_one]

/-- The action specialization is the original monoidal action evaluated at the point. -/
theorem translation_eq (p : 𝟙_ C ⟶ G) :
    translation (X := X) p = (λ_ X).inv ≫ p ▷ X ≫ γ[G, X] := by
  rw [translation, Hom.smul_def, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- An equivariant morphism intertwines the translations of both full objects. -/
@[reassoc] theorem translation_naturality {Y : C} [ModObj G Y]
    (f : X ⟶ Y) [IsModHom G f] (p : 𝟙_ C ⟶ G) :
    translation p ≫ f = f ≫ translation p := by
  rw [comp_translation, translation, IsModHom.map_smul, Category.id_comp]

end FLT.Mazur.GroupActionPointTranslation
