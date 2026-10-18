/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PullbackOneLegTransport

/-!
# Transport a full intersection from its left boundary square

The monic right chart determines the second boundary. Keeping this orientation
explicit avoids inferring large geometric chart types through two flips.
-/

@[expose] public section
open CategoryTheory Limits
namespace FLT.Mazur.PullbackOneLegTransport
universe v u
variable {C : Type u} [Category.{v} C]
  {P X Y Z P' X' Y' Z' : C}
  {l : P ⟶ X} {r : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  {l' : P' ⟶ X'} {r' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/-- The full pullback transports from its left leg and a monic right chart. -/
theorem of_left [Mono g'] (h : IsPullback l r f g)
    (e : P ≅ P') (a : X ≅ X') (b : Y ≅ Y') (c : Z ≅ Z')
    (hl : l ≫ a.hom = e.hom ≫ l')
    (hf : f ≫ c.hom = a.hom ≫ f') (hg : g ≫ c.hom = b.hom ≫ g')
    (hw : l' ≫ f' = r' ≫ g') : IsPullback l' r' f' g' := by
  exact (of_right h.flip e b a c hl hg hf hw.symm).flip

end FLT.Mazur.PullbackOneLegTransport
