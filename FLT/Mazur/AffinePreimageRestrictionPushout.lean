/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSectionTopComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Actual section pushouts for affine preimage restrictions

Restricting an affine morphism along an inclusion of affine base opens gives
a pushout of the original section rings. The maps are the actual presheaf
restrictions, not independently chosen localization presentations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffinePreimageRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D S : Scheme} (g : D ⟶ S) [IsAffineHom g]
  {U V : S.affineOpens} (h : V ≤ U)

omit [IsAffineHom g] in
/-- The nested restriction square of the original family is cartesian. -/
theorem isPullback :
    IsPullback (D.homOfLE (g.preimage_mono h)) (g ∣_ V.1)
      (g ∣_ U.1) (S.homOfLE h) := by
  apply IsPullback.of_right (h₁₂ := (g ⁻¹ᵁ U.1).ι) (h₂₂ := U.1.ι)
  · simpa only [Scheme.homOfLE_ι] using (isPullback_morphismRestrict g V.1).flip
  · exact (morphismRestrict_homOfLE g V.1 U.1 h).symm
  · exact (isPullback_morphismRestrict g U.1).flip

/-- Affine restriction is a pushout on the exact original coordinate rings. -/
theorem sections_isPushout :
    IsPushout (g.app U.1) (S.presheaf.map (homOfLE h).op)
      (D.presheaf.map (homOfLE (g.preimage_mono h)).op) (g.app V.1) := by
  let _ : IsAffine (g ⁻¹ᵁ U.1).toScheme := U.2.preimage g
  let _ : IsAffine (g ⁻¹ᵁ V.1).toScheme := V.2.preimage g
  have H := isPushout_appTop_of_isPullback (isPullback g h)
  apply H.of_iso U.1.topIso (g ⁻¹ᵁ U.1).topIso V.1.topIso (g ⁻¹ᵁ V.1).topIso
  · ext x
    symm
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] using!
      Approximation.topIso_hom_resLE g U.1 (g ⁻¹ᵁ U.1) le_rfl x
  · ext x
    symm
    exact Approximation.topIso_hom_restriction h x
  · ext x
    symm
    exact Approximation.topIso_hom_restriction (g.preimage_mono h) x
  · ext x
    symm
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] using!
      Approximation.topIso_hom_resLE g V.1 (g ⁻¹ᵁ V.1) le_rfl x

end FLT.Mazur.AffinePreimageRestriction
