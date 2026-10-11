/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleOpenCohomologyRestriction

/-!
# Structure cohomology through an isomorphism with specified ring scalars

Transport retains the original coefficient homomorphism, including when
that homomorphism factors through a residue field.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.FCurve

universe u

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- Restriction by a scheme isomorphism preserves the specified ring action. -/
def moduleRingHRestrictIsoEquiv (e : X ≅ Y) (ρ : R →+* Γ(Y, ⊤))
    (M : Y.Modules) (q : ℕ) :
    ModuleRingH ρ M q ≃ₗ[R]
      ModuleRingH (e.hom.appTop.hom.comp ρ) (M.restrict e.hom) q := by
  refine { toAddEquiv := moduleHIsoEquiv e M q, map_smul' := ?_ }
  intro r x
  exact moduleHIsoEquiv_smul e M q (ρ r) x

/-- Actual structure cohomology transports with its original ring scalars. -/
def structureRingHIsoEquiv (e : X ≅ Y) (ρ : R →+* Γ(Y, ⊤)) (q : ℕ) :
    ModuleRingH ρ (structureUnitModule Y) q ≃ₗ[R]
      ModuleRingH (e.hom.appTop.hom.comp ρ) (structureUnitModule X) q :=
  (moduleRingHRestrictIsoEquiv e ρ (structureUnitModule Y) q).trans
    (((moduleRingHFunctor (e.hom.appTop.hom.comp ρ) q).mapIso
      (Scheme.Modules.restrictUnitIso e.hom)).toLinearEquiv)

/-- Equal coefficient homomorphisms give the identity on underlying cohomology. -/
def moduleRingHScalarsCongr (ρ σ : R →+* Γ(X, ⊤)) (h : ρ = σ)
    (M : X.Modules) (q : ℕ) : ModuleRingH ρ M q ≃ₗ[R] ModuleRingH σ M q :=
  h ▸ LinearEquiv.refl R (ModuleRingH ρ M q)

end FLT.Mazur.FCurve
