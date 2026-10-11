/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRingCohomologyFinite
public import FLT.Mazur.WeierstrassSpecSections

/-!
# Structural coefficients through a commuting diagram

These identities keep large scheme constructions out of definitional
reduction when transporting their original coefficients.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.Chow.AffineBase

open WeierstrassIntegralChart

variable {R : Type} [CommRing R] {X Y Z : Scheme}

/-- The two spectrum coefficient conventions agree on an arbitrary structure morphism. -/
theorem baseCohomologyScalars_eq_specSectionHom (f : X ⟶ Spec (.of R)) :
    baseCohomologyScalars f = specSectionHom f := rfl

/-- A commuting diagram transports the whole original coefficient map. -/
theorem appTop_comp_scalars (e : X ⟶ Y) (i : Y ⟶ Z) (f : X ⟶ Z)
    (he : e ≫ i = f) (ρ : R →+* Γ(Z, ⊤)) :
    e.appTop.hom.comp (i.appTop.hom.comp ρ) = f.appTop.hom.comp ρ := by
  subst f
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Coefficients of an actual closed inclusion can be transported through any factorization. -/
theorem factor_scalar_transport (e : X ⟶ Y) (i : Y ⟶ Z) (f : X ⟶ Z)
    (he : e ≫ i = f) (g : Z ⟶ Spec (.of R)) (σ : R →+* Γ(X, ⊤))
    (hs : ∀ a, f.appTop (specSectionHom g a) = σ a) :
    e.appTop.hom.comp (i.appTop.hom.comp (baseCohomologyScalars g)) = σ := by
  rw [appTop_comp_scalars e i f he, baseCohomologyScalars_eq_specSectionHom]
  exact RingHom.ext hs

end FLT.Mazur.Chow.AffineBase
