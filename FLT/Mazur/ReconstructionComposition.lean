/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Composing reconstruction squares

A chain of reconstruction squares identifies the two composite maps after
applying the reconstruction functor. The calculation is independent of sheaves.
-/

public section
open CategoryTheory
universe u v u' v'
namespace FLT.Mazur.ReconstructionComposition
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Three reconstruction squares and the chart square give composite reconstruction. -/
theorem square (F : C ⥤ D) {A₀ A₁ A₂ B₀ B₁ : C} {M N : D}
    (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂) (k : A₂ ⟶ B₁) (h : A₀ ⟶ B₀) (l : B₀ ⟶ B₁)
    (e : F.obj B₁ ⟶ N) (e₂ : F.obj A₂ ⟶ M) (e₁ : F.obj A₁ ⟶ M)
    (e₀ : F.obj A₀ ⟶ M) (eB : F.obj B₀ ⟶ N) (t : M ⟶ N)
    (hk : F.map k ≫ e = e₂ ≫ t) (hg : F.map g ≫ e₂ = e₁)
    (hf : F.map f ≫ e₁ = e₀) (hl : F.map l ≫ e = eB)
    (ht : e₀ ≫ t = F.map h ≫ eB) :
    F.map (f ≫ g ≫ k) ≫ e = F.map (h ≫ l) ≫ e := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hk, ← Category.assoc (F.map g), hg, ← Category.assoc (F.map f), hf, ht, hl]

end FLT.Mazur.ReconstructionComposition
