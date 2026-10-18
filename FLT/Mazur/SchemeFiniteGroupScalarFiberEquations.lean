/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupClosedScalarFiber
public import FLT.Mazur.OriginalScalarFiberRadical

/-!
# Original power equations for stable closed scalar fibers

The ideal of the actual closed orbit image gives equations for whole original
scalar-fiber containment. Failure constructs a point outside the original locus
at exactly the same scalar prime, rather than just at a generization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood OriginalScalarFiberRadical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  (ρ : G →* Aut X) (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)

/-- The defining ideal of the constructed closed image in the invariant spectrum. -/
def closedOrbitIdeal : Ideal (invariantCoordinates ρ) :=
  PrimeSpectrum.vanishingIdeal (closedOrbitImage ρ Z hZ : Set (quotient ρ))

/-- Its equations recover exactly the complete orbit image, without replacing the source. -/
theorem closedOrbitIdeal_zeroLocus :
    PrimeSpectrum.zeroLocus (closedOrbitIdeal ρ Z hZ : Set _) =
      (closedOrbitImage ρ Z hZ : Set (quotient ρ)) := by
  rw [closedOrbitIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (closedOrbitImage ρ Z hZ).isClosed.closure_eq

/-- The defining equations test every actual invariant prime. -/
theorem mem_closedOrbitImage_iff_ideal (Q : PrimeSpectrum (invariantCoordinates ρ)) :
    Q ∈ closedOrbitImage ρ Z hZ ↔ closedOrbitIdeal ρ Z hZ ≤ Q.asIdeal := by
  change (closedOrbitImage ρ Z hZ : Set (quotient ρ)) Q ↔ _
  rw [← closedOrbitIdeal_zeroLocus]
  rfl

variable {R : Type} [CommRing R] (s : R →+* invariantCoordinates ρ)
local notation "s₀" => invariantScalarCoordinates ρ s

include hstable in
/-- Whole original scalar-fiber containment is equivalent to exact original power equations. -/
theorem scalar_fiber_subset_iff_power (P : PrimeSpectrum R) :
    (∀ x : X, scalarMorphism s₀ x = P → x ∈ Z) ↔
      ∀ b ∈ closedOrbitIdeal ρ Z hZ,
        ∃ (n : ℕ) (r : R), r ∉ P.asIdeal ∧ s r * b ^ n ∈ P.asIdeal.map s := by
  rw [scalar_fiber_subset_iff ρ Z hZ hstable s P]
  simp_rw [mem_closedOrbitImage_iff_ideal]
  constructor
  · intro h b hb
    apply (forall_fiber_primes_iff_power s P.asIdeal b).mp
    intro Q hQ
    exact h Q (PrimeSpectrum.ext hQ) hb
  · intro h Q hQ b hb
    apply (forall_fiber_primes_iff_power s P.asIdeal b).mpr (h b hb) Q
    exact congrArg PrimeSpectrum.asIdeal hQ

include hstable in
/-- A failed power equation constructs a bad original source point at the exact scalar center. -/
theorem exists_scalar_fiber_point_of_no_power (P : PrimeSpectrum R)
    (b : invariantCoordinates ρ) (hb : b ∈ closedOrbitIdeal ρ Z hZ)
    (h : ∀ (n : ℕ) (r : R), r ∉ P.asIdeal → s r * b ^ n ∉ P.asIdeal.map s) :
    ∃ x : X, scalarMorphism s₀ x = P ∧ x ∉ Z := by
  by_contra hn
  push Not at hn
  obtain ⟨n, r, hr, he⟩ :=
    (scalar_fiber_subset_iff_power ρ Z hZ hstable s P).mp hn b hb
  exact h n r hr he

end FLT.Mazur.SchemeFiniteGroupQuotient
