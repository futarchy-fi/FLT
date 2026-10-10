/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Restriction of comparisons conjugated by two outer isomorphisms

A commuting middle square and two outer squares give a square for the
comparison between the outer objects. The two outer isomorphisms are independent.
-/

@[expose] public section
open CategoryTheory
namespace FLT.Mazur.AffineComparisonConjugation

/-- Conjugating a compatible middle comparison preserves its restriction square. -/
theorem restriction {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {a₀ a₁ a₂ a₃ : A} {b₀ b₁ b₂ b₃ : B}
    (e₀ : a₀ ≅ a₁) (e₁ : a₁ ≅ a₂) (e₂ : a₃ ≅ a₂)
    (d₀ : b₀ ≅ b₁) (d₁ : b₁ ≅ b₂) (d₂ : b₃ ≅ b₂)
    (n₀ : F.obj a₀ ≅ b₀) (n₃ : F.obj a₃ ≅ b₃)
    (l : F.obj a₁ ≅ b₁) (r : F.obj a₂ ≅ b₂)
    (h₀ : F.map e₀.hom ≫ l.hom = n₀.hom ≫ d₀.hom)
    (h₁ : F.map e₁.hom ≫ r.hom = l.hom ≫ d₁.hom)
    (h₂ : F.map e₂.hom ≫ r.hom = n₃.hom ≫ d₂.hom) :
    F.map (e₀ ≪≫ e₁ ≪≫ e₂.symm).hom ≫ n₃.hom =
      n₀.hom ≫ (d₀ ≪≫ d₁ ≪≫ d₂.symm).hom := by
  apply (cancel_mono d₂.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← h₂, ← Functor.map_comp_assoc F e₂.inv e₂.hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, h₁, ← Category.assoc, h₀,
    Category.assoc]


end FLT.Mazur.AffineComparisonConjugation
