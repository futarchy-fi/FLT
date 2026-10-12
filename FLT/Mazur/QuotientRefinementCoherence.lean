/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.EpiMono

/-!
# Categorical coherence for normalized quotient projections

These calculations isolate inverse comparison and epi cancellation from the
concrete tensor and sheaf constructions to which they apply.
-/

@[expose] public section
open CategoryTheory
namespace FLT.Mazur.QuotientRefinementCoherence
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Invert a composable triple of comparison isomorphisms. -/
theorem inverse_triple {W X Y Z : C} (a : W ≅ X) (b : X ≅ Y)
    (c : Y ≅ Z) (e : W ≅ Z) (h : a.hom ≫ b.hom ≫ c.hom = e.hom) :
    c.inv ≫ b.inv ≫ a.inv = e.inv := by
  apply (cancel_mono e.hom).mp
  conv_lhs => rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- Refining a normalized projection uses only comparison naturality. -/
theorem projection_refine (F : C ⥤ D) {A Q : C} {B A' Q' : D}
    (q : A ⟶ Q) (a : B ⟶ F.obj A) (b : A' ⟶ B)
    (c : F.obj A ⟶ A') (e : F.obj Q ⟶ Q') (q' : A' ⟶ Q')
    (hn : F.map q ≫ e = c ≫ q') (hc : b ≫ a ≫ c = 𝟙 A') :
    b ≫ (a ≫ F.map q) ≫ e = q' := by
  simp only [Category.assoc] at hc ⊢
  rw [hn, ← Category.assoc a, ← Category.assoc b, hc, Category.id_comp]

/-- A transition is preserved by refinement when both epi projections are preserved. -/
theorem transition_refine (F : C ⥤ D) {A Q P : C} {B Q' P' : D}
    (q : A ⟶ Q) (p : A ⟶ P) (t : Q ⟶ P) (a : B ⟶ F.obj A)
    (cq : F.obj Q ⟶ Q') (cp : F.obj P ⟶ P')
    (q' : B ⟶ Q') (p' : B ⟶ P') (t' : Q' ⟶ P')
    [Epi (a ≫ F.map q)] (ht : q ≫ t = p)
    (hq : a ≫ F.map q ≫ cq = q') (hp : a ≫ F.map p ≫ cp = p')
    (ht' : q' ≫ t' = p') : F.map t ≫ cp = cq ≫ t' := by
  apply (cancel_epi (a ≫ F.map q)).mp
  simp only [Category.assoc]
  rw [← Category.assoc (F.map q), ← F.map_comp, ht, hp]
  rw [← hq] at ht'
  simpa only [Category.assoc] using ht'.symm

end FLT.Mazur.QuotientRefinementCoherence
