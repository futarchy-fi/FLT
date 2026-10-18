/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalScalarFiberRadical
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite equations for whole original scalar fibers

A finitely generated support ideal needs only its actual generators tested.
Their original power equations can share one denominator outside the original
prime. This does not assume that the scalar map is integral or surjective.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.OriginalScalarFiberRadical
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
  (G : Finset B) (J : Ideal B) (hG : Ideal.span (G : Set B) = J)

include hG in
/-- Testing the chosen generators suffices for the entire support ideal. -/
theorem fiber_ideal_iff_generator_powers :
    (∀ Q : PrimeSpectrum B, Q.asIdeal.comap s = P → J ≤ Q.asIdeal) ↔
      ∀ b ∈ G, ∃ (n : ℕ) (r : R), r ∉ P ∧ s r * b ^ n ∈ P.map s := by
  constructor
  · intro h b hb
    apply (forall_fiber_primes_iff_power s P b).mp
    intro Q hQ
    apply h Q hQ
    rw [← hG]
    exact Ideal.subset_span hb
  · intro h Q hQ
    rw [← hG]
    apply Ideal.span_le.mpr
    intro b hb
    exact (forall_fiber_primes_iff_power s P b).mpr (h b hb) Q hQ

omit J hG in
/-- All finite generator equations can use the same avoiding original denominator. -/
theorem exists_common_power_denominator
    (h : ∀ b ∈ G, ∃ (n : ℕ) (r : R), r ∉ P ∧ s r * b ^ n ∈ P.map s) :
    ∃ r : R, r ∉ P ∧ ∀ b ∈ G, ∃ n : ℕ, s r * b ^ n ∈ P.map s := by
  classical
  choose n r hr he using (fun b : G ↦ h b.val b.property)
  let a : R := ∏ b : G, r b
  have ha : a ∉ P := P.primeCompl.prod_mem (fun b _ ↦ hr b)
  refine ⟨a, ha, fun b hb ↦ ⟨n ⟨b, hb⟩, ?_⟩⟩
  have hd : r ⟨b, hb⟩ ∣ a := Finset.dvd_prod_of_mem r (Finset.mem_univ (⟨b, hb⟩ : G))
  obtain ⟨c, hc⟩ := hd
  rw [hc, map_mul, mul_right_comm]
  exact (P.map s).mul_mem_right (s c) (he ⟨b, hb⟩)

include hG in
/-- Whole-fiber containment has finitely many equations with one original denominator. -/
theorem fiber_ideal_iff_common_denominator :
    (∀ Q : PrimeSpectrum B, Q.asIdeal.comap s = P → J ≤ Q.asIdeal) ↔
      ∃ r : R, r ∉ P ∧ ∀ b ∈ G, ∃ n : ℕ, s r * b ^ n ∈ P.map s := by
  rw [fiber_ideal_iff_generator_powers s P G J hG]
  refine ⟨exists_common_power_denominator s P G, ?_⟩
  rintro ⟨r, hr, h⟩ b hb
  obtain ⟨n, hn⟩ := h b hb
  exact ⟨n, r, hr, hn⟩

end FLT.Mazur.OriginalScalarFiberRadical
