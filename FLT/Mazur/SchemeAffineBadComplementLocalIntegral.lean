/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralFiber
public import FLT.Mazur.SchemeAffineBadComplementCoordinates

/-!
# Bad-complement denominators from integrality at one original prime

The bad quotient need only become integral after localizing at the specified
original prime. Whole-fiber containment produces a scalar outside that prime
vanishing on the exact chosen bad thickening.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (J : Ideal Γ(X, ⊤)) (O : X.Opens)
  (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ)

omit [IsAffine X] in
include hJ in
/-- The bad image is exactly the spectrum image of the explicit quotient scalar map. -/
theorem scalar_badImage_eq_quotient_range :
    scalarMorphism s '' (O : Set X)ᶜ =
      Set.range (PrimeSpectrum.comap ((Ideal.Quotient.mk J).comp s)) := by
  change (PrimeSpectrum.comap s ∘ X.toSpecΓ) '' (O : Set X)ᶜ = _
  rw [Set.image_comp, ← hJ, PrimeSpectrum.comap_comp, Set.range_comp]
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

omit [IsAffine X] in
include hJ in
/-- Whole-fiber containment can be tested in the exact bad quotient ring. -/
theorem affineBad_fiber_empty_iff (P : PrimeSpectrum R) :
    (∀ x : X, scalarMorphism s x = P → x ∈ O) ↔
      ∀ Q : PrimeSpectrum (Γ(X, ⊤) ⧸ J),
        Q.asIdeal.comap ((Ideal.Quotient.mk J).comp s) ≠ P.asIdeal := by
  have he := scalar_badImage_eq_quotient_range s J O hJ
  constructor
  · intro h Q hQ
    have hmem : P ∈ scalarMorphism s '' (O : Set X)ᶜ := by
      rw [he]
      exact ⟨Q, PrimeSpectrum.ext hQ⟩
    obtain ⟨x, hx, hxP⟩ := hmem
    exact hx (h x hxP)
  · intro h x hx
    by_contra hxo
    have hmem : P ∈ scalarMorphism s '' (O : Set X)ᶜ := ⟨x, hxo, hx⟩
    rw [he] at hmem
    obtain ⟨Q, hQ⟩ := hmem
    exact h Q (congrArg PrimeSpectrum.asIdeal hQ)

include hJ in
/-- Integrality only at the chosen original prime constructs an exact bad-ideal denominator. -/
theorem exists_scalar_of_badQuotient_local_integral (P : PrimeSpectrum R)
    (hInt : (OriginalPrimeIntegralFiber.localizedMap
      ((Ideal.Quotient.mk J).comp s) P.asIdeal).IsIntegral)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ s r ∈ J ∧ X.basicOpen (s r) ≤ O := by
  obtain ⟨r, hr, hz⟩ := OriginalPrimeIntegralFiber.exists_kernel_scalar
    ((Ideal.Quotient.mk J).comp s) P.asIdeal hInt
      ((affineBad_fiber_empty_iff s J O hJ P).mp hP)
  have hrJ : s r ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hz
  refine ⟨r, hr, hrJ, (mem_scalarAvoidanceIdeal_iff s O r).mp ?_⟩
  rw [scalarAvoidanceIdeal_eq_affineBad_comap s J O hJ]
  exact Ideal.le_radical hrJ

include hJ in
/-- Local bad-quotient integrality supplies the safe original prime used by open lifting. -/
theorem mem_scalarNeighborhoodLocus_of_badQuotient_local_integral (P : PrimeSpectrum R)
    (hInt : (OriginalPrimeIntegralFiber.localizedMap
      ((Ideal.Quotient.mk J).comp s) P.asIdeal).IsIntegral)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    P ∈ scalarNeighborhoodLocus s O := by
  obtain ⟨r, hr, _, hO⟩ := exists_scalar_of_badQuotient_local_integral s J O hJ P hInt hP
  exact (mem_scalarNeighborhoodLocus_iff s O P).mpr ⟨r, hr, hO⟩

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
