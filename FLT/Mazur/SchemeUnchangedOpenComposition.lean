/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Composing full unchanged-open comparisons

These abstract lemmas seal the restriction bookkeeping before applying it
to large glued schemes and recursively constructed finite modifications.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SchemeUnchangedOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z T : Scheme}

/-- Full unchanged-open comparisons compose over the same target open. -/
theorem isIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (hf : IsIso (f ∣_ g ⁻¹ᵁ U)) (hg : IsIso (g ∣_ U)) : IsIso ((f ≫ g) ∣_ U) := by
  rw [morphismRestrict_comp]
  infer_instance

/-- A scheme isomorphism before an unchanged contraction preserves the full comparison. -/
theorem isIso_precomp (e : X ≅ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (hg : IsIso (g ∣_ U)) : IsIso ((e.hom ≫ g) ∣_ U) :=
  isIso_comp e.hom g U inferInstance hg

/-- Express the complete identity pullback using a specified target open. -/
theorem isIso_of_identity_pullback_eq (f : X ⟶ Y) (i : T ⟶ Y) [IsOpenImmersion i]
    (j : T ⟶ X) (H : IsPullback (𝟙 T) j i f) (U : Y.Opens) (hU : i.opensRange = U) :
    IsIso (f ∣_ U) := by
  rw [← hU]
  exact isIso_of_identity_pullback f i j H

end FLT.Mazur.SchemeUnchangedOpen
