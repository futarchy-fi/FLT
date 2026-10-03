/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicFractionFieldComplete

/-!
# Convergence of the local logarithm

On the principal-unit neighborhood v(u - 1) < v(p), logarithm terms
are bounded by a geometric sequence. Completeness is derived from the
complete DVR, rather than assumed for its fraction field.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Filter IsLocalRing IsDedekindDomain
open scoped Topology WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [CharZero L] in
/-- The valuation of n+1 is at least v(p)^n. -/
theorem dvr_valuation_succ_lower (n : ℕ) :
    ((dvrPrime S).valuation L (p : L)) ^ n ≤
      (dvrPrime S).valuation L ((n + 1 : ℕ) : L) := by
  rw [dvr_valuation_natCast S L p (n + 1) (by omega)]
  apply pow_le_pow_right_of_le_one'
  · rw [← map_natCast (algebraMap S L)]
    exact HeightOneSpectrum.valuation_le_one (dvrPrime S) (p : S)
  · have h := (padicValNat_le_nat_log (n + 1) (p := p)).trans_lt
      (Nat.log_lt_self p (by omega))
    omega

/-- The n-th logarithm term for log(1+x), indexed starting with x. -/
def localLogTerm {L : Type*} [Field L] (x : L) (n : ℕ) : L :=
  (-1 : L) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : L)

/-- A geometric bound uniform for all x with v(x) ≤ v(a). -/
theorem localLogTerm_le (x a : L)
    (hx : (dvrPrime S).valuation L x ≤ (dvrPrime S).valuation L a) (n : ℕ) :
    (dvrPrime S).valuation L (localLogTerm x n) ≤
      (dvrPrime S).valuation L (a * (a / (p : L)) ^ n) := by
  simp only [localLogTerm, map_div₀, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
  rw [pow_succ, mul_comm (_ ^ n), div_pow, ← mul_div_assoc]
  apply div_le_div₀ zero_le (mul_le_mul' hx (pow_le_pow_left₀ zero_le hx n))
    (pow_pos (localExpRadius_pos S L p) n) (dvr_valuation_succ_lower S L p n)

/-- The logarithm terms tend to zero in the actual adic topology. -/
theorem localLogTerms_tendsto_zero (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    letI := dvrAdicValued S L
    Tendsto (localLogTerm x) atTop (𝓝 0) := by
  let := dvrAdicValued S L
  have hr : Valued.v (x / (p : L)) < 1 := by
    change (dvrPrime S).valuation L _ < 1
    rwa [map_div₀, div_lt_one₀ (localExpRadius_pos S L p)]
  apply valuation_tendsto_zero_of_le
    (by simpa using (Valued.tendsto_zero_pow_of_v_lt_one hr).const_mul x)
  exact localLogTerm_le S L p x x le_rfl

variable [IsAdicComplete (maximalIdeal S) S]

/-- The logarithm series converges on an explicit principal-unit neighborhood. -/
theorem localLog_summable (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    letI := dvrAdicValued S L
    Summable (localLogTerm x) := by
  let := dvrAdicValued S L
  let : CompleteSpace L := adicFractionFieldComplete S L
  let : NonarchimedeanRing L := ((dvrPrime S).valuation L).subgroups_basis.nonarchimedean
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using localLogTerms_tendsto_zero S L p x hx

end LocalClassFieldTheory
