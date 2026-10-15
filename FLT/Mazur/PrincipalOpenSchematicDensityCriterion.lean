/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RegularPrincipalOpenLiftExt

/-!
# Schematic density of a principal open detects regularity

The converse to regular principal-open density retains all nilpotents:
an affine schematic dominance hypothesis forces the actual ring map
to be injective. Applied to localization, this detects regularity of
the original denominator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PrincipalOpenSchematicDensityCriterion
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- Affine schematic dominance is exactly injectivity of the original ring homomorphism. -/
theorem spec_iff (f : A →+* B) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f)) ↔
      Function.Injective f := by
  constructor
  · intro hf
    let _ := hf
    have ha : Mono (Spec.map (CommRingCat.ofHom f)).appTop :=
      ConcreteCategory.mono_of_injective _ ((Spec.map (CommRingCat.ofHom f)).app_injective ⊤)
    have hb : Mono (CommRingCat.ofHom f) :=
      (MorphismProperty.monomorphisms _).arrow_mk_iso_iff
        (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom f)) |>.mpr ha
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp hb
  · exact SurjectiveDominantEpi.spec_schematic f

/-- The actual principal open is schematically dense exactly when its denominator is regular. -/
theorem inclusion_iff (a : A) :
    IsSchemeTheoreticallyDominant (PrincipalAffineRefinement.inclusion a) ↔ IsRegular a := by
  rw [PrincipalAffineRefinement.inclusion, spec_iff,
    IsLocalization.injective_iff_isRegular (Submonoid.powers a)]
  constructor
  · intro h
    exact h ⟨a, ⟨1, pow_one a⟩⟩
  · intro h c
    obtain ⟨k, hk⟩ := c.property
    exact hk ▸ h.pow k

end FLT.Mazur.PrincipalOpenSchematicDensityCriterion
