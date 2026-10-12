/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeUnchangedOpenComposition

/-!
# Transporting unchanged opens through a square of isomorphisms

Seal restriction bookkeeping before applying it to recursively glued models.
The transported open is the actual inverse image under the target isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SchemeUnchangedOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme}

/-- An isomorphism of contractions transports the entire unchanged target open. -/
theorem isIso_of_iso_square (e : X' ≅ X) (a : Y' ≅ Y) (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : e.hom ≫ f = g ≫ a.hom) (U : Y.Opens) (hf : IsIso (f ∣_ U)) :
    IsIso (g ∣_ a.hom ⁻¹ᵁ U) := by
  have hc := isIso_precomp e f U hf
  rw [h, morphismRestrict_comp] at hc
  exact IsIso.of_isIso_comp_right _ (a.hom ∣_ U)

end FLT.Mazur.SchemeUnchangedOpen
