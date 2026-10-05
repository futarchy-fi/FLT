/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffineBase

/-!
# Ample sections on affine pieces of a cartesian square

If an affine open of the new base maps into an affine open of the original
base, its source restriction is an affine pullback of an ample sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
variable {X Y S T : Scheme.{0}} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T} {L : X.Modules}

/-- Affine pieces of a cartesian square carry the actual pulled-back ample sections. -/
theorem RelativelyAmpleLineBundle.ample_cartesian_affineOpen
    (hL : RelativelyAmpleLineBundle f L) (sq : IsPullback p q f g)
    (V : S.Opens) (hV : IsAffineOpen V) (W : T.Opens) (hW : IsAffineOpen W)
    (hWV : W ≤ g ⁻¹ᵁ V) :
    AmpleLineBundle (((Scheme.Modules.pullback p).obj L).restrict (q ⁻¹ᵁ W).ι) := by
  let : IsAffine V.toScheme := hV
  let : IsAffine W.toScheme := hW
  have hle : q ⁻¹ᵁ W ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
    exact q.preimage_mono hWV
  let p' := p.resLE (f ⁻¹ᵁ V) (q ⁻¹ᵁ W) hle
  have hs : IsPullback p' (q ∣_ W) (f ∣_ V) (g.resLE V W hWV) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE sq hWV (le_rfl : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V)
        (inf_eq_right.mpr hle).symm
  have : IsAffineHom p' := MorphismProperty.of_isPullback hs.flip inferInstance
  exact ((hL.2.2 V hV).pullback_affine p').of_iso
    (modulePullbackRestrictIso p p' (q ⁻¹ᵁ W).ι (f ⁻¹ᵁ V).ι
      (p.resLE_comp_ι hle).symm L)

end FLT.Mazur.FCurve
