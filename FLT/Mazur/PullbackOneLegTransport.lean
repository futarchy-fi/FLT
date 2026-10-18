/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Transport a full intersection using one boundary square

When the new chart is monic, the other boundary square follows from the
commuting intersection square. All four comparison maps remain isomorphisms.
-/

@[expose] public section
open CategoryTheory Limits
namespace FLT.Mazur.PullbackOneLegTransport
universe v u
variable {C : Type u} [Category.{v} C]
  {P X Y Z P' X' Y' Z' : C}
  {l : P ⟶ X} {r : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  {l' : P' ⟶ X'} {r' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/-- A monic target chart determines the missing boundary square uniquely. -/
theorem of_right [Mono f'] (h : IsPullback l r f g)
    (e : P ≅ P') (a : X ≅ X') (b : Y ≅ Y') (c : Z ≅ Z')
    (hr : r ≫ b.hom = e.hom ≫ r')
    (hf : f ≫ c.hom = a.hom ≫ f') (hg : g ≫ c.hom = b.hom ≫ g')
    (hw : l' ≫ f' = r' ≫ g') : IsPullback l' r' f' g' := by
  apply h.of_iso e a b c ?_ hr hf hg
  apply (cancel_mono f').mp
  rw [Category.assoc, ← hf, ← Category.assoc, h.w, Category.assoc, hg,
    ← Category.assoc r, hr, Category.assoc, ← hw, Category.assoc]

/-- Full boundary transport composes without replacing either puncture. -/
theorem arrow_trans {O A B D : C} (p : O ⟶ A) (q : O ⟶ B) (r : O ⟶ D)
    (a : A ≅ B) (b : B ≅ D) (e f : O ≅ O)
    (ha : p ≫ a.hom = e.hom ≫ q) (hb : q ≫ b.hom = f.hom ≫ r) :
    p ≫ (a ≪≫ b).hom = (e ≪≫ f).hom ≫ r := by
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ha, Category.assoc, hb,
    Category.assoc]

end FLT.Mazur.PullbackOneLegTransport
