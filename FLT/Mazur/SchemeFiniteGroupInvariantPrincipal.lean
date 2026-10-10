/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupPrincipalQuotient
public import FLT.Mazur.SchemeFiniteGroupQuotientOrbits

/-!
# Invariant principal neighborhoods in affine scheme charts

Stable opens have a neighborhood basis cut out by invariant global functions.
The quotient of each such principal open is the corresponding principal open
in the actual invariant-coordinate spectrum.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} (ρ : G →* Aut X)

/-- Pulling back the quotient principal open gives the original invariant principal open. -/
lemma quotientMap_preimage_basicOpen (r : invariantCoordinates ρ) :
    quotientMap ρ ⁻¹ᵁ PrimeSpectrum.basicOpen r = X.basicOpen (r : Γ(X, ⊤)) := by
  change X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (r : Γ(X, ⊤)) = _
  exact Scheme.toSpecΓ_preimage_basicOpen X (r : Γ(X, ⊤))

variable [Finite G] [IsAffine X]

/-- Invariant principal opens form a basis inside stable opens of an affine scheme. -/
theorem exists_invariant_principal (U : X.Opens)
    (hU : ∀ (g : G) (x : X), x ∈ U → (ρ g).hom x ∈ U) (x : X) (hx : x ∈ U) :
    ∃ r : invariantCoordinates ρ,
      x ∈ X.basicOpen (r : Γ(X, ⊤)) ∧ X.basicOpen (r : Γ(X, ⊤)) ≤ U := by
  obtain ⟨_, ⟨r, rfl⟩, hrx, hrU⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := invariantCoordinates ρ)).isOpen_iff.mp
      (quotientMap_image_isOpen ρ U U.isOpen hU) (quotientMap ρ x) ⟨x, hx, rfl⟩
  refine ⟨r, ?_, ?_⟩
  · rw [← quotientMap_preimage_basicOpen]
    exact hrx
  · rw [← quotientMap_preimage_basicOpen]
    intro y hy
    have hy' : y ∈ quotientMap ρ ⁻¹' (quotientMap ρ '' (U : Set X)) := hrU hy
    rwa [quotientMap_saturated ρ U hU] at hy'

/-- The image of the actual principal quotient map is the expected principal open. -/
lemma principalQuotientMap_opensRange (r : invariantCoordinates ρ) :
    (principalQuotientMap ρ r).opensRange = PrimeSpectrum.basicOpen r := by
  ext y
  change y ∈ Set.range (principalQuotientMap ρ r) ↔ y ∈ PrimeSpectrum.basicOpen r
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := (quotientMap (principalAction ρ r)).surjective z
    change (quotientMap (principalAction ρ r) ≫ principalQuotientMap ρ r) x ∈ _
    rw [show quotientMap (principalAction ρ r) ≫ principalQuotientMap ρ r =
      (X.basicOpen (r : Γ(X, ⊤))).ι ≫ quotientMap ρ from
        quotientMap_naturality _ _ _ (principal_ι_equivariant ρ r)]
    exact Eq.mpr (congrArg (fun V : X.Opens ↦ x.1 ∈ V)
      (quotientMap_preimage_basicOpen ρ r)) x.property
  · intro hy
    obtain ⟨x, rfl⟩ := (quotientMap ρ).surjective y
    have hx : x ∈ X.basicOpen (r : Γ(X, ⊤)) := by
      rw [← quotientMap_preimage_basicOpen]
      exact hy
    refine ⟨quotientMap (principalAction ρ r) ⟨x, hx⟩, ?_⟩
    exact congrArg (fun k ↦ k ⟨x, hx⟩)
      (quotientMap_naturality _ _ _ (principal_ι_equivariant ρ r))

end FLT.Mazur.SchemeFiniteGroupQuotient
