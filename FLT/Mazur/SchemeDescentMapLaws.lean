/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGeometricDescentData

/-!
# Identity, composition, and inversion of geometric descent maps

Compatibility with the original overlap is stable under the category operations.
An invertible compatible sheaf map has a compatible inverse.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {M N P : Y.Modules}
variable (D : Data p M) (E : Data p N) (F : Data p P)

/-- The identity sheaf map intertwines every descent overlap. -/
lemma mapCompatible_id : D.MapCompatible p D (𝟙 M) := by
  simp only [MapCompatible, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Compatible descent maps compose. -/
lemma mapCompatible_comp (f : M ⟶ N) (g : N ⟶ P)
    (hf : D.MapCompatible p E f) (hg : E.MapCompatible p F g) :
    D.MapCompatible p F (f ≫ g) := by
  unfold MapCompatible at hf hg ⊢
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hf, Category.assoc, hg,
    Category.assoc]

/-- The inverse of an overlap-compatible isomorphism is overlap-compatible. -/
lemma mapCompatible_inv (e : M ≅ N) (he : D.MapCompatible p E e.hom) :
    E.MapCompatible p D e.inv := by
  unfold MapCompatible at he ⊢
  apply (cancel_epi ((pullback (Limits.pullback.fst p p)).map e.hom)).mp
  rw [← Category.assoc, ← he]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id, ← Functor.map_comp_assoc, Category.id_comp]

end FLT.Mazur.SchemeGeometricDescent.Data
