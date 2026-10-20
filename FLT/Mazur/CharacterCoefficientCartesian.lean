/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeBaseChange

/-!
# The original character coefficient square is Cartesian

The actual coefficient map, rather than an unspecified isomorphism of
character schemes, exhibits arbitrary coefficient extension as base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.CharacterSchemeBaseChange

open CharacterAlgebraScalarExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable (R A G : Type u) [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid G]

/-- The specified coefficient morphism is the original Cartesian source comparison. -/
theorem coefficientMap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (coeff R A G).toRingHom))
      (model A G).hom (model R G).hom (baseMap R A) := by
  apply IsPullback.of_iso_pullback _ (schemeIso R A G ≪≫ pullbackSymmetry _ _)
  · change (schemeIso R A G).hom ≫ (pullbackSymmetry _ _).hom ≫ _ = _
    rw [pullbackSymmetry_hom_comp_fst, schemeIso_snd]
  · change (schemeIso R A G).hom ≫ (pullbackSymmetry _ _).hom ≫ _ = _
    rw [pullbackSymmetry_hom_comp_snd, schemeIso_fst]
  · constructor
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (coeff R A G).commutes a

end FLT.Mazur.CharacterSchemeBaseChange
