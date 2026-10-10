/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalQuadratic
public import FLT.Mazur.PowerSeriesLeadingComposition
public import FLT.Mazur.PrimeCharacteristicScalar
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Divisibility of the low coefficients of the formal p-series

Commutation with integer multiplication forces every coefficient below degree p
to vanish in characteristic p. Applying this to the quotient by (p) gives
integer-p divisibility, which is stronger than membership in the maximal ideal.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The actual multiplication series commutes with changing coefficient rings. -/
theorem map_multiplicationSeries {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    PowerSeries.map f (multiplicationSeries W n) = multiplicationSeries (W.map f) n := by
  unfold multiplicationSeries PowerSeries.map
  rw [map_multiply W f n (by simp [PowerSeries.X])]
  simp only [PowerSeries.X, MvPowerSeries.map_X]

/-- The formal p-series has no terms below degree p in characteristic p. -/
theorem coeff_multiplicationSeries_prime_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p]
    (k : ℕ) (hk : k < p) : PowerSeries.coeff k (multiplicationSeries W p) = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hz (n : ℕ) : PowerSeries.constantCoeff (multiplicationSeries W n) = 0 :=
      constantCoeff_multiply W n (by simp [PowerSeries.X])
    by_cases hk0 : k = 0
    · subst k
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hz p
    by_cases hk1 : k = 1
    · subst k
      simp
    have hk2 : 1 < k := by omega
    obtain ⟨m, hm⟩ := exists_prime_scalar_pow_sub_unit p k hk2 hk R
    have hl (i : ℕ) (hi : i < k) : PowerSeries.coeff i (multiplicationSeries W p) = 0 :=
      ih i hi (hi.trans hk)
    have he := congrArg (PowerSeries.coeff k) (multiplicationSeries_comp_comm W p m)
    rw [coeff_subst_of_outer_vanishing _ _ k (hz m) hl,
      coeff_subst_of_inner_vanishing _ _ k (by omega) hl,
      coeff_one_multiplicationSeries] at he
    apply hm.mul_right_eq_zero.mp
    linear_combination he

/-- Every coefficient of degree below p is divisible by the integer p over any ring. -/
theorem prime_dvd_coeff_multiplicationSeries (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : k < p) : (p : R) ∣ PowerSeries.coeff k (multiplicationSeries W p) := by
  let I : Ideal R := Ideal.span {(p : R)}
  apply Ideal.mem_span_singleton.mp
  change PowerSeries.coeff k (multiplicationSeries W p) ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rcases subsingleton_or_nontrivial (R ⧸ I) with h | h
  · exact Subsingleton.elim _ _
  · have hp0 : (p : R ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    let _ : CharP (R ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
    have he := congrArg (PowerSeries.coeff k) (map_multiplicationSeries W (Ideal.Quotient.mk I) p)
    rw [PowerSeries.coeff_map,
      coeff_multiplicationSeries_prime_eq_zero (W.map (Ideal.Quotient.mk I)) p k hk] at he
    exact he

end FLT.Mazur.FormalInfinity
