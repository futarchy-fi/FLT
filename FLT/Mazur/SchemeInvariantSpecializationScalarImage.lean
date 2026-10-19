/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeInvariantClosedScalarImage

/-!
# Scalar images of full invariant prime closures

A scalar prime in the image of the closure of Q has a source character over
its own residue closure whose invariant center still specializes Q. Thus
passing to the scalar residue closure retains the prescribed closed branch.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X : Scheme} [IsAffine X] (ρ : G →* Aut X)
  (σ : R →+* invariantCoordinates ρ)
local notation "s" => invariantScalarCoordinates ρ σ

/-- Exact scalar lifts in the entire prescribed invariant specialization locus. -/
theorem exists_scalar_character_of_invariant_specialization (hs : (s).FiniteType)
    (Q : PrimeSpectrum (invariantCoordinates ρ)) (P : PrimeSpectrum R)
    (hP : ∃ Q' : PrimeSpectrum (invariantCoordinates ρ),
      Q.asIdeal ≤ Q'.asIdeal ∧ PrimeSpectrum.comap σ Q' = P) :
    ∃ w : Γ(X, ⊤) →+* scalarResidueClosure P,
      w.comp s = algebraMap R (scalarResidueClosure P) ∧
      Q.asIdeal ≤ (quotientMap ρ (sourceCharacterMap w default)).asIdeal := by
  let Z : Set X := quotientMap ρ ⁻¹' PrimeSpectrum.zeroLocus (Q.asIdeal : Set _)
  have hZ : IsClosed Z :=
    (PrimeSpectrum.isClosed_zeroLocus (Q.asIdeal : Set _)).preimage (quotientMap ρ).continuous
  have hz : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z := by
    intro g x hx
    change quotientMap ρ ((ρ g).hom x) ∈ PrimeSpectrum.zeroLocus (Q.asIdeal : Set _)
    rw [← Scheme.Hom.comp_apply, quotientMap_invariant]
    exact hx
  have hp : P ∈ PrimeSpectrum.comap σ '' (closedOrbitImage ρ Z hZ : Set (quotient ρ)) := by
    obtain ⟨Q', hQ', he⟩ := hP
    obtain ⟨x, hx⟩ := (quotientMap ρ).surjective Q'
    refine ⟨Q', ⟨x, ?_, hx⟩, he⟩
    change quotientMap ρ x ∈ PrimeSpectrum.zeroLocus (Q.asIdeal : Set _)
    rw [hx]
    exact hQ'
  obtain ⟨w, hw, hc⟩ := exists_scalar_character_of_closedOrbit ρ Z hZ hz σ hs P hp
  exact ⟨w, hw, hc⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
