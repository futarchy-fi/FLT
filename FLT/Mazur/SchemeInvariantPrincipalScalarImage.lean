/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupPrincipalCharacterLifts
public import FLT.Mazur.SchemeFiniteGroupClosedScalarFiber
public import FLT.Mazur.ScalarResidueClosureGeometry

/-!
# Principal invariant images in the prescribed scalar spectrum

Every scalar prime in the image of an invariant principal open has a source
character inside that same open over its own scalar residue closure. Finite
type constructs this character without embedding an invariant residue field
in the smaller scalar closure. No minimality or scalar flatness is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X : Scheme} [IsAffine X] (ρ : G →* Aut X)
  (σ : R →+* invariantCoordinates ρ) (t : invariantCoordinates ρ)
local notation "s" => invariantScalarCoordinates ρ σ

omit [Finite G] in
/-- Full-character agreement gives the exact scalar morphism for any original scalar map. -/
theorem invariantCharacter_scalarMorphism {F : Type} [Field F]
    (χ : invariantCoordinates ρ →+* F) (w : Γ(X, ⊤) →+* F)
    (hw : ∀ r : invariantCoordinates ρ, w r.val = χ r) :
    sourceCharacterMap w ≫ scalarMorphism s = Spec.map (CommRingCat.ofHom (χ.comp σ)) := by
  rw [sourceCharacterMap_scalar]
  apply congrArg Spec.map
  ext r
  exact hw (σ r)

/-- The principal source image is computed in the unchanged original scalar spectrum. -/
theorem invariant_principal_scalar_image :
    scalarMorphism s '' (X.basicOpen t.val : Set X) =
      PrimeSpectrum.comap σ '' (PrimeSpectrum.basicOpen t : Set _) := by
  rw [scalarMorphism_through_quotient]
  ext P
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨quotientMap ρ x, ?_, rfl⟩
    change x ∈ quotientMap ρ ⁻¹ᵁ PrimeSpectrum.basicOpen t
    rwa [quotientMap_preimage_basicOpen]
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨x, rfl⟩ := (quotientMap ρ).surjective Q
    refine ⟨x, ?_, rfl⟩
    rw [← quotientMap_preimage_basicOpen]
    exact hQ

attribute [local semireducible] scalarResidueClosure

/-- All scalar primes in this image have exact characters over their own residue closures. -/
theorem exists_scalar_character_of_invariant_principal (hs : (s).FiniteType)
    (P : PrimeSpectrum R)
    (hP : P ∈ PrimeSpectrum.comap σ '' (PrimeSpectrum.basicOpen t : Set _)) :
    ∃ w : Γ(X, ⊤) →+* scalarResidueClosure P,
      w.comp s = algebraMap R (scalarResidueClosure P) ∧
      sourceCharacterMap w default ∈ X.basicOpen t.val := by
  rw [← invariant_principal_scalar_image ρ σ t] at hP
  obtain ⟨x, hx, he⟩ := hP
  exact exists_scalar_character_in_open s P hs (X.basicOpen t.val) x hx he

end FLT.Mazur.SchemeFiniteGroupQuotient
