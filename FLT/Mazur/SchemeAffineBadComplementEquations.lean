/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralGenerators
public import FLT.Mazur.SchemeAffineBadComplementLocalIntegral

/-!
# Original safe neighborhoods from bad-quotient equations

Equations on algebra generators construct the needed local integrality.
For finitely many generators, their leading-coefficient product gives an
explicit open where whole-fiber containment is exactly the safe-prime test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (J : Ideal Γ(X, ⊤)) (O : X.Opens)
  (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ)
set_option quotPrecheck false
local notation "q" => (Ideal.Quotient.mk J).comp s

include hJ in
/-- Equations on quotient generators replace the local integrality input. -/
theorem exists_scalar_of_badQuotient_equations (S : Set (Γ(X, ⊤) ⧸ J))
    (hgen : Subring.closure (Set.range q ∪ S) = ⊤) (P : PrimeSpectrum R)
    (heq : ∀ b ∈ S, ∃ p : R[X], p.eval₂ q b = 0 ∧ p.leadingCoeff ∉ P.asIdeal)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ s r ∈ J ∧ X.basicOpen (s r) ≤ O :=
  exists_scalar_of_badQuotient_local_integral s J O hJ P
    (OriginalPrimeIntegralFiber.localizedMap_integral_of_generator_equations
      q P.asIdeal S hgen heq) hP

include hJ in
/-- One finite product specifies where the quotient equations construct exact bad denominators. -/
theorem exists_scalar_of_badQuotient_finite_equations {I : Type*} [Fintype I]
    (b : I → Γ(X, ⊤) ⧸ J) (p : I → R[X])
    (hgen : Subring.closure (Set.range q ∪ Set.range b) = ⊤)
    (heq : ∀ i, (p i).eval₂ q (b i) = 0) (P : PrimeSpectrum R)
    (hlead : (∏ i, (p i).leadingCoeff) ∉ P.asIdeal)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ s r ∈ J ∧ X.basicOpen (s r) ≤ O :=
  exists_scalar_of_badQuotient_local_integral s J O hJ P
    (OriginalPrimeIntegralFiber.localizedMap_integral_of_finite_equations
      q P.asIdeal b p hgen heq hlead) hP

include hJ in
/-- On the explicit coefficient open, whole fibers exactly characterize safe original primes. -/
theorem mem_scalarNeighborhoodLocus_iff_fiber_of_finite_equations
    {I : Type*} [Fintype I] (b : I → Γ(X, ⊤) ⧸ J) (p : I → R[X])
    (hgen : Subring.closure (Set.range q ∪ Set.range b) = ⊤)
    (heq : ∀ i, (p i).eval₂ q (b i) = 0) (P : PrimeSpectrum R)
    (hlead : (∏ i, (p i).leadingCoeff) ∉ P.asIdeal) :
    P ∈ scalarNeighborhoodLocus s O ↔ ∀ x : X, scalarMorphism s x = P → x ∈ O := by
  constructor
  · intro h x hx
    obtain ⟨r, hr, hO⟩ := (mem_scalarNeighborhoodLocus_iff s O P).mp h
    apply hO
    rw [← scalarMorphism_preimage]
    change scalarMorphism s x ∈ PrimeSpectrum.basicOpen r
    change r ∉ (scalarMorphism s x).asIdeal
    rwa [hx]
  · intro hP
    obtain ⟨r, hr, _, hO⟩ := exists_scalar_of_badQuotient_finite_equations
      s J O hJ b p hgen heq P hlead hP
    exact (mem_scalarNeighborhoodLocus_iff s O P).mpr ⟨r, hr, hO⟩

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
