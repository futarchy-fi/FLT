/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePreimageRestrictionPushout

/-!
# Cartesian preimage charts with their actual section maps

An arbitrary base change of an affine family gives a pushout on every pair
of compatible affine base opens. The four maps are the original app and
appLE maps, so this applies directly to pullbacks of ideal sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineCartesianPreimage
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D E S T : Scheme} {g : D ⟶ S} {q : E ⟶ T} {i : E ⟶ D} {f : T ⟶ S}
  (H : IsPullback i q g f) (V : S.affineOpens) (U : T.affineOpens) (h : U.1 ≤ f ⁻¹ᵁ V.1)

include H h in
/-- The total preimage chart maps into the corresponding original family chart. -/
theorem preimage_le : q ⁻¹ᵁ U.1 ≤ i ⁻¹ᵁ g ⁻¹ᵁ V.1 := by
  rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  exact q.preimage_mono h

variable [IsAffineHom g] [IsAffineHom q]

/-- The affine coordinate square for arbitrary compatible base charts is a pushout. -/
theorem sections_isPushout :
    IsPushout (g.app V.1) (f.appLE V.1 U.1 h)
      (i.appLE (g ⁻¹ᵁ V.1) (q ⁻¹ᵁ U.1) (preimage_le H V U h)) (q.app U.1) := by
  let _ : IsAffine (g ⁻¹ᵁ V.1).toScheme := V.2.preimage g
  let _ : IsAffine (q ⁻¹ᵁ U.1).toScheme := U.2.preimage q
  have hs : q ⁻¹ᵁ U.1 = i ⁻¹ᵁ (g ⁻¹ᵁ V.1) ⊓ q ⁻¹ᵁ U.1 :=
    (inf_eq_right.mpr (preimage_le H V U h)).symm
  have P := isPushout_appTop_of_isPullback (Scheme.Hom.isPullback_resLE H h le_rfl hs)
  apply P.of_iso V.1.topIso (g ⁻¹ᵁ V.1).topIso U.1.topIso (q ⁻¹ᵁ U.1).topIso
  · ext x
    symm
    simpa only [Scheme.Hom.appLE_eq_app] using!
      Approximation.topIso_hom_resLE g V.1 (g ⁻¹ᵁ V.1) le_rfl x
  · ext x
    exact (Approximation.topIso_hom_resLE f V.1 U.1 h x).symm
  · ext x
    exact (Approximation.topIso_hom_resLE i (g ⁻¹ᵁ V.1) (q ⁻¹ᵁ U.1)
      (preimage_le H V U h) x).symm
  · ext x
    symm
    simpa only [Scheme.Hom.appLE_eq_app] using!
      Approximation.topIso_hom_resLE q U.1 (q ⁻¹ᵁ U.1) le_rfl x

end FLT.Mazur.AffineCartesianPreimage
