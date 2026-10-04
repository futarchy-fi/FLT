/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.AssociatedPrimeDimension
public import FLT.Mathlib.RingTheory.Regular.ParameterIdealDimension

/-! # The first parameter avoids associated primes at full depth -/

@[expose] public section

universe u

namespace RingTheory.Sequence

open IsLocalRing

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A full-depth parameter cannot belong to an associated prime. -/
theorem parameter_head_notMem_associatedPrime {x : R} {rs : List R}
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R)
    [IsArtinianRing (R ⧸ (Module.annihilator R M ⊔ Ideal.ofList (x :: rs)))]
    (hex : ∃ qs : List R, qs.length = rs.length + 1 ∧ IsRegular M qs)
    {p : Ideal R} (hp : IsAssociatedPrime p M) : x ∉ p := by
  intro hx
  have := hp.isPrime
  obtain ⟨qs, hlen, hreg⟩ := hex
  have hlo := hreg.length_le_dimension_quotient_associatedPrime hp
  have hhi := ringKrullDim_quotient_le_parameter_tail (I := Module.annihilator R M)
    (by simpa only [Submodule.annihilator_top] using hp.annihilator_le) hx hm
  have hbad := hlo.trans hhi
  rw [hlen] at hbad
  have : rs.length + 1 ≤ rs.length := by exact_mod_cast hbad
  omega

/-- The first member of a full-depth parameter list is a nonzerodivisor. -/
theorem isSMulRegular_parameter_head {x : R} {rs : List R}
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R)
    [IsArtinianRing (R ⧸ (Module.annihilator R M ⊔ Ideal.ofList (x :: rs)))]
    (hex : ∃ qs : List R, qs.length = rs.length + 1 ∧ IsRegular M qs) :
    IsSMulRegular M x := by
  by_contra h
  have hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact h
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨hp, hxp⟩ := Set.mem_iUnion.mp hp
  exact parameter_head_notMem_associatedPrime hm hex hp hxp

end RingTheory.Sequence
