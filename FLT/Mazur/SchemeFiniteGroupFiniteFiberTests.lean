/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupScalarFiberEquations
public import FLT.Mazur.OriginalScalarFiberFiniteEquations
public import Mathlib.Topology.NoetherianSpace

/-!
# Constructed finite tests for whole original scalar fibers

Noetherianity of the original affine scheme constructs finitely many invariant
functions defining the stable closed locus. No Noetherian hypothesis on the
invariant ring or the original scalar ring is needed. Whole-fiber containment
has finitely many power equations sharing one original avoiding denominator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood OriginalScalarFiberRadical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  [NoetherianSpace X] (ρ : G →* Aut X) (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)

/-- The actual invariant spectrum is Noetherian as a topological quotient of the original chart. -/
theorem quotient_noetherianSpace : NoetherianSpace (quotient ρ) :=
  noetherianSpace_of_surjective (quotientMap ρ)
    (quotientMap ρ).continuous (quotientMap ρ).surjective

/-- Finitely many invariant functions define the full closed orbit image. -/
theorem exists_closedOrbit_finite_tests :
    ∃ a : Finset (invariantCoordinates ρ),
      PrimeSpectrum.zeroLocus (a : Set _) =
        (closedOrbitImage ρ Z hZ : Set (quotient ρ)) := by
  let _ := quotient_noetherianSpace ρ
  obtain ⟨a, ha⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp
    ⟨NoetherianSpace.isCompact ((closedOrbitImage ρ Z hZ : Set (quotient ρ))ᶜ),
      (closedOrbitImage ρ Z hZ).isClosed.isOpen_compl⟩
  exact ⟨a, compl_injective ha⟩

/-- Fix the finite support equations before choosing the original scalar prime. -/
def closedOrbitTests : Finset (invariantCoordinates ρ) :=
  (exists_closedOrbit_finite_tests ρ Z hZ).choose

/-- The selected functions recover exactly the original complete orbit image. -/
theorem closedOrbitTests_zeroLocus :
    PrimeSpectrum.zeroLocus (closedOrbitTests ρ Z hZ : Set _) =
      (closedOrbitImage ρ Z hZ : Set (quotient ρ)) :=
  (exists_closedOrbit_finite_tests ρ Z hZ).choose_spec

/-- Membership is tested by the finitely many fixed invariant functions. -/
theorem mem_closedOrbitImage_iff_tests (Q : PrimeSpectrum (invariantCoordinates ρ)) :
    Q ∈ closedOrbitImage ρ Z hZ ↔ ∀ b ∈ closedOrbitTests ρ Z hZ, b ∈ Q.asIdeal := by
  change (closedOrbitImage ρ Z hZ : Set (quotient ρ)) Q ↔ _
  rw [← closedOrbitTests_zeroLocus]
  rfl

variable {R : Type} [CommRing R] (s : R →+* invariantCoordinates ρ)
local notation "s₀" => invariantScalarCoordinates ρ s

include hstable in
/-- Whole original scalar-fiber containment has a finite exact power test. -/
theorem scalar_fiber_subset_iff_finite_powers (P : PrimeSpectrum R) :
    (∀ x : X, scalarMorphism s₀ x = P → x ∈ Z) ↔
      ∀ b ∈ closedOrbitTests ρ Z hZ,
        ∃ (n : ℕ) (r : R), r ∉ P.asIdeal ∧ s r * b ^ n ∈ P.asIdeal.map s := by
  rw [scalar_fiber_subset_iff ρ Z hZ hstable s P]
  simp_rw [mem_closedOrbitImage_iff_tests]
  constructor
  · intro h b hb
    apply (forall_fiber_primes_iff_power s P.asIdeal b).mp
    intro Q hQ
    exact h Q (PrimeSpectrum.ext hQ) b hb
  · intro h Q hQ b hb
    apply (forall_fiber_primes_iff_power s P.asIdeal b).mpr (h b hb) Q
    exact congrArg PrimeSpectrum.asIdeal hQ

include hstable in
/-- The finite tests can share one denominator in the unchanged original scalar ring. -/
theorem scalar_fiber_subset_iff_common_power_denominator (P : PrimeSpectrum R) :
    (∀ x : X, scalarMorphism s₀ x = P → x ∈ Z) ↔
      ∃ r : R, r ∉ P.asIdeal ∧ ∀ b ∈ closedOrbitTests ρ Z hZ,
        ∃ n : ℕ, s r * b ^ n ∈ P.asIdeal.map s := by
  rw [scalar_fiber_subset_iff_finite_powers ρ Z hZ hstable s P]
  refine ⟨exists_common_power_denominator s P.asIdeal _, ?_⟩
  rintro ⟨r, hr, h⟩ b hb
  obtain ⟨n, hn⟩ := h b hb
  exact ⟨n, r, hr, hn⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
