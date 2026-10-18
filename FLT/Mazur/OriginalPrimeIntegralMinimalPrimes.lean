/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralComponents
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Original local integrality from domain components

There are finitely many minimal primes in a Noetherian target. Testing the
corresponding domain quotients suffices, even if the original target has
nilpotents and the original scalar ring is not Noetherian.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]

/-- The minimal components intersect in precisely the nilpotent ideal. -/
theorem minimal_component_intersection :
    (⨅ Q : minimalPrimes B, Q.val) = nilradical B := by
  rw [iInf_subtype, ← sInf_eq_iInf, Ideal.sInf_minimalPrimes]
  rfl

/-- Finitely many minimal components suffice to construct original local integrality. -/
theorem localizedMap_integral_iff_minimal_components (hfin : (minimalPrimes B).Finite) :
    (localizedMap s P).IsIntegral ↔ ∀ Q ∈ minimalPrimes B,
      (localizedMap ((Ideal.Quotient.mk Q).comp s) P).IsIntegral := by
  let _ := hfin.fintype
  rw [localizedMap_integral_iff_components s P (fun Q : minimalPrimes B ↦ Q.val)
    (minimal_component_intersection.le)]
  exact Subtype.forall

/-- Noetherianity is needed only in the target, not in the original scalar ring. -/
theorem localizedMap_integral_iff_minimalPrimes [IsNoetherianRing B] :
    (localizedMap s P).IsIntegral ↔ ∀ Q ∈ minimalPrimes B,
      (localizedMap ((Ideal.Quotient.mk Q).comp s) P).IsIntegral :=
  localizedMap_integral_iff_minimal_components s P (minimalPrimes.finite_of_isNoetherianRing B)

/-- Component equations on the original generators construct integrality of the full target. -/
theorem localizedMap_integral_of_minimal_generator_equations
    (hfin : (minimalPrimes B).Finite) (S : Set B)
    (hgen : Subring.closure (Set.range s ∪ S) = ⊤)
    (he : ∀ b ∈ S, ∀ Q ∈ minimalPrimes B, ∃ p : R[X],
      p.eval₂ ((Ideal.Quotient.mk Q).comp s) (Ideal.Quotient.mk Q b) = 0 ∧
        p.leadingCoeff ∉ P) :
    (localizedMap s P).IsIntegral := by
  classical
  let _ := hfin.fintype
  apply localizedMap_integral_of_generator_equations s P S hgen
  intro b hb
  have hex (Q : minimalPrimes B) := he b hb Q.val Q.property
  choose p hp using hex
  apply exists_equation_of_component_equations s P (fun Q : minimalPrimes B ↦ Q.val)
    minimal_component_intersection.le b p _ (fun Q ↦ (hp Q).2)
  intro Q
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hom_eval₂]
  exact (hp Q).1

/-- Failure has a fixed original generator and a domain component with no avoiding equation. -/
theorem exists_minimal_generator_obstruction (hfin : (minimalPrimes B).Finite) (S : Set B)
    (hgen : Subring.closure (Set.range s ∪ S) = ⊤)
    (h : ¬ (localizedMap s P).IsIntegral) :
    ∃ b ∈ S, ∃ Q ∈ minimalPrimes B, ∀ p : R[X],
      p.eval₂ ((Ideal.Quotient.mk Q).comp s) (Ideal.Quotient.mk Q b) = 0 →
        p.leadingCoeff ∈ P := by
  classical
  by_contra hn
  apply h
  apply localizedMap_integral_of_minimal_generator_equations s P hfin S hgen
  push Not at hn
  exact hn

end FLT.Mazur.OriginalPrimeIntegralFiber
