/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Specializing actions through monoidal functors

Evaluation at an arbitrary group section commutes with a monoidal functor and
with a monoidal natural transformation. No origin for that section is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory
namespace FLT.Mazur.MonoidalActionSpecialization
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Evaluate an action morphism at a specified section of its acting object. -/
def specialize {G X : C} (a : G ⊗ X ⟶ X) (c : 𝟙_ C ⟶ G) : X ⟶ X :=
  (λ_ X).inv ≫ c ▷ X ≫ a

/-- An equivariant square retains evaluation at an arbitrary section. -/
theorem specialize_equivariant {G X H Y : C} (a : G ⊗ X ⟶ X) (b : H ⊗ Y ⟶ Y)
    (u : G ⟶ H) (v : X ⟶ Y) (w : a ≫ v = (u ⊗ₘ v) ≫ b) (c : 𝟙_ C ⟶ G) :
    specialize a c ≫ v = v ≫ specialize b (c ≫ u) := by
  simp only [specialize, Category.assoc, w, whiskerRight_comp_tensorHom_assoc]
  rw [tensorHom_def']
  simp only [Category.assoc, leftUnitor_inv_naturality_assoc]

/-- A monoidal functor preserves evaluation at a section, including the unit comparison. -/
theorem map_specialize (F : C ⥤ D) [F.Monoidal] {G X : C}
    (a : G ⊗ X ⟶ X) (c : 𝟙_ C ⟶ G) :
    specialize (Functor.LaxMonoidal.μ F G X ≫ F.map a)
      (Functor.LaxMonoidal.ε F ≫ F.map c) = F.map (specialize a c) := by
  simp only [specialize, Functor.map_comp, comp_whiskerRight, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.left_unitality_inv_assoc]

/-- Monoidal naturality transports evaluation even for a section only defined in the target. -/
theorem specialize_naturality (F H : C ⥤ D) [F.Monoidal] [H.Monoidal]
    (e : F ⟶ H) [e.IsMonoidal] {G X : C} (a : G ⊗ X ⟶ X)
    (c : 𝟙_ D ⟶ F.obj G) :
    specialize (Functor.LaxMonoidal.μ F G X ≫ F.map a) c ≫ e.app X =
      e.app X ≫ specialize (Functor.LaxMonoidal.μ H G X ≫ H.map a) (c ≫ e.app G) := by
  apply specialize_equivariant
  rw [Category.assoc, e.naturality a, ← Category.assoc, NatTrans.IsMonoidal.tensor]
  simp only [Category.assoc]

end FLT.Mazur.MonoidalActionSpecialization
