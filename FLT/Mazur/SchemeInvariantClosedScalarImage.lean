/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarClosedGeometricLifts
public import FLT.Mazur.SchemeInvariantPrincipalScalarImage
public import FLT.Mazur.SchemeFiniteGroupScalarFiberEquations

/-!
# Exact scalar lifts on stable closed loci

The image of the full invariant closed locus has source characters over the
original scalar prime's own residue closure. All closed equations are retained;
the full invariant prime may change when descending to this smaller field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X : Scheme} [IsAffine X] (ρ : G →* Aut X)
  (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)
  (σ : R →+* invariantCoordinates ρ)
local notation "C" => invariantCoordinates ρ
local notation "s" => invariantScalarCoordinates ρ σ
local notation "i" => invariantScalarCoordinates ρ (RingHom.id C)
local notation "J" => closedOrbitIdeal ρ Z hZ
attribute [local semireducible] scalarResidueClosure

include hstable in
/-- Every prime in the original scalar image of a closed orbit locus has an exact closed lift. -/
theorem exists_scalar_character_of_closedOrbit (hs : (s).FiniteType)
    (P : PrimeSpectrum R)
    (hP : P ∈ PrimeSpectrum.comap σ '' (closedOrbitImage ρ Z hZ : Set (quotient ρ))) :
    ∃ w : Γ(X, ⊤) →+* scalarResidueClosure P,
      w.comp s = algebraMap R (scalarResidueClosure P) ∧ sourceCharacterMap w default ∈ Z := by
  obtain ⟨Q, hQ, hQP⟩ := hP
  obtain ⟨x, hx⟩ := (quotientMap ρ).surjective Q
  have hJ : (J).map i ≤ (X.isoSpec.hom x).asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hm : r ∈ Q.asIdeal := by
      change Q ∈ (closedOrbitImage ρ Z hZ : Set (quotient ρ)) at hQ
      rw [← closedOrbitIdeal_zeroLocus] at hQ
      exact hQ hr
    change r ∈ (quotientMap ρ x).asIdeal
    rwa [hx]
  have hp : PrimeSpectrum.comap s (X.isoSpec.hom x) = P := by
    change PrimeSpectrum.comap σ (quotientMap ρ x) = P
    rwa [hx]
  obtain ⟨w, hw, hj⟩ := exists_scalar_character_on_closed s hs ((J).map i) P
    (X.isoSpec.hom x) hp hJ
  refine ⟨w, hw, ?_⟩
  rw [← closedOrbitImage_preimage ρ Z hZ hstable]
  change (sourceCharacterMap w ≫ quotientMap ρ) default ∈
    (closedOrbitImage ρ Z hZ : Set (quotient ρ))
  rw [sourceCharacterMap_quotient, ← closedOrbitIdeal_zeroLocus]
  intro r hr
  exact hj (i r) (Ideal.mem_map_of_mem i hr)

end FLT.Mazur.SchemeFiniteGroupQuotient
