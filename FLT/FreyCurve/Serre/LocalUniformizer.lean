/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.LocalResidue
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# The prime as a uniformizer

The canonical integers of the completion of `ℚ` at `p` identify with `ℤ_[p]`.
Consequently `p` does not lie in the square of their maximal ideal.
-/

@[expose] public section

open NumberField IsLocalRing ValuativeRel
open Rat.HeightOneSpectrum
attribute [local instance] completionValuativeRel completion_isNonarchimedeanLocalField
set_option quotPrecheck false
namespace NumberField
variable (p : ℕ) (hp : p.Prime)
local notation "v" => hp.toHeightOneSpectrumRingOfIntegersRat
local notation "K" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "R" => 𝒪[K]
/-- The rational prime has valuation one in the canonical integers of its completion. -/
theorem prime_notMem_square_maximalIdeal : (p : R) ∉ maximalIdeal R ^ 2 := by
  let q : Nat.Primes := primesEquiv v
  let : Fact (Nat.Prime (q : ℕ)) := ⟨q.property⟩
  have hmem : (p : 𝓞 ℚ) ∈ (v).asIdeal := by
    change Rat.ringOfIntegersEquiv (p : 𝓞 ℚ) ∈ Ideal.span {(p : ℤ)}
    rw [map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hm := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem
  rw [map_natCast] at hm
  have hqp : (q : ℕ) = p :=
    (Nat.prime_dvd_prime_iff_eq q.property hp).mp ((natGenerator_dvd_iff v).mpr hm)
  let e : R ≃+* ℤ_[q] := (completionIntegerEquiv v).trans
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  have hi : Irreducible (p : R) := by
    apply (MulEquiv.irreducible_iff e).mp
    rw [map_natCast, ← hqp]
    exact PadicInt.irreducible_p
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer (p : R)).mp hi,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨a, ha⟩
  have he : (p : R) * a = 1 := by
    apply mul_left_cancel₀ hi.ne_zero
    linear_combination -ha
  exact hi.not_isUnit (⟨⟨(p : R), a, he, by rwa [mul_comm]⟩, rfl⟩)
end NumberField

