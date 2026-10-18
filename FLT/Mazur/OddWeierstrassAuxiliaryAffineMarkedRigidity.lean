/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryAffineCubicIso
public import FLT.Mazur.OddWeierstrassAuxiliaryMarkedRigidity

/-!
# Rigidity of the original auxiliary-marked affine-source families

The actual affine cubic comparison detects family isomorphisms. Proper marked
rigidity therefore gives uniqueness before choosing normalized coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} [IsAffine T] (f g : T ⟶ levelThree.left)
  (e d : (auxiliarySchemeGroup f).X ≅ (auxiliarySchemeGroup g).X)

/-- The original cubic projections detect equality of actual affine-source family comparisons. -/
theorem auxiliaryAffineCubicIso_injective
    (h : auxiliaryAffineCubicIso f g e = auxiliaryAffineCubicIso f g d) : e = d := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (auxiliarySchemeOriginalCubicProjection g)).mp
  rw [← auxiliaryAffineCubicIso_projection, ← auxiliaryAffineCubicIso_projection, h]

/-- Two actual affine-source family isomorphisms preserving the auxiliary labels are equal. -/
theorem auxiliaryAffineMarkedIso_unique
    (he : ∀ c : Labels 3, auxiliarySchemeMarking f c ≫ e.hom = auxiliarySchemeMarking g c)
    (hd : ∀ c : Labels 3, auxiliarySchemeMarking f c ≫ d.hom = auxiliarySchemeMarking g c) :
    e = d :=
  auxiliaryAffineCubicIso_injective f g e d
    (auxiliaryMarkedProperIso_unique f.appTop.hom g.appTop.hom
      (auxiliaryAffineCubicIso f g e) (auxiliaryAffineCubicIso f g d)
      (auxiliaryAffineCubicIso_base f g e) (auxiliaryAffineCubicIso_zero f g e he)
      (auxiliaryAffineCubicIso_section f g e he)
      (auxiliaryAffineCubicIso_base f g d) (auxiliaryAffineCubicIso_zero f g d hd)
      (auxiliaryAffineCubicIso_section f g d hd))

/-- The original affine-source family has no nontrivial automorphism fixing its full frame. -/
theorem auxiliaryAffineMarkedIso_eq_refl
    (e : (auxiliarySchemeGroup f).X ≅ (auxiliarySchemeGroup f).X)
    (he : ∀ c : Labels 3, auxiliarySchemeMarking f c ≫ e.hom = auxiliarySchemeMarking f c) :
    e = Iso.refl _ :=
  auxiliaryAffineMarkedIso_unique f f e (Iso.refl _) he (fun _ ↦ Category.comp_id _)

end FLT.Mazur.OddWeierstrassParameter
