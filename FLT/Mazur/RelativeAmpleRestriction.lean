/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffineBase
public import FLT.Mazur.ProperAmpleConverse

/-!
# Restricting relative ampleness to base opens

The affine opens of a restricted base are affine opens of the original base.
The comparison uses the actual iterated restriction of the coefficient sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X S : Scheme} {f : X ⟶ S} {L : X.Modules}

/-- Relative section ampleness restricts to every open of the base. -/
theorem RelativelyAmpleLineBundle.restrict (hL : RelativelyAmpleLineBundle f L)
    (U : S.Opens) : RelativelyAmpleLineBundle (f ∣_ U) (L.restrict (f ⁻¹ᵁ U).ι) := by
  let := hL.1
  refine ⟨inferInstance, hL.2.1.restrict _, fun V hV ↦ ?_⟩
  let W := (f ∣_ U) ⁻¹ᵁ V
  let e : W.toScheme ≅ (f ⁻¹ᵁ U.ι ''ᵁ V).toScheme :=
    ((f ⁻¹ᵁ U).ι.isoImage W) ≪≫ X.isoOfEq (image_morphismRestrict_preimage f U V)
  have he : W.ι ≫ (f ⁻¹ᵁ U).ι = e.hom ≫ (f ⁻¹ᵁ U.ι ''ᵁ V).ι := by
    simp [e, W]
  exact ((hL.2.2 _ (U.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hV)).restrict_affine
    e.hom).of_iso
    (((restrictFunctorComp W.ι (f ⁻¹ᵁ U).ι).app L).symm ≪≫
      (restrictFunctorCongr he).app L ≪≫
      (restrictFunctorComp e.hom (f ⁻¹ᵁ U.ι ''ᵁ V).ι).app L)

/-- Closed power presentations restrict to every open of the base. -/
theorem RelativeAmple.restrict (hL : RelativeAmple f L) (hline : LocallyFreeRankOne L)
    (U : S.Opens) : RelativeAmple (f ∣_ U) (L.restrict (f ⁻¹ᵁ U).ι) := by
  let := hL.isProper
  exact ((hL.relativelyAmpleLineBundle hline).restrict U).relativeAmple

end FLT.Mazur.FCurve
