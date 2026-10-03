/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DvrAdicTopology
public import FLT.LocalClassFieldTheory.DvrFactorialValuation
public import FLT.LocalClassFieldTheory.ValuationSeriesComparison
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# An explicit local exponential convergence domain

For residue characteristic p and characteristic-zero fraction field, the
factorial estimate bounds x^n/n! by (x/p)^n in valuation. Thus the terms
tend to zero on v(x) < v(p), and the series converges when the actual adic
field topology is complete. No analytic convergence assumption is used.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Filter IsLocalRing
open scoped Topology WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [CharP (ResidueField S) p] in
/-- The residue-prime value defining the convergence domain is strictly positive. -/
theorem localExpRadius_pos : 0 < (dvrPrime S).valuation L (p : L) := by
  apply pos_iff_ne_zero.mpr
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- The exponential terms tend to zero on the explicit domain v(x) < v(p). -/
theorem localExpTerms_tendsto_zero (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    letI := dvrAdicValued S L
    Tendsto (fun n : ℕ => x ^ n / (n.factorial : L)) atTop (𝓝 0) := by
  let := dvrAdicValued S L
  have hratio : Valued.v (x / (p : L)) < 1 := by
    change (dvrPrime S).valuation L (x / (p : L)) < 1
    rw [map_div₀, div_lt_one₀ (localExpRadius_pos S L p)]
    exact hx
  apply valuation_tendsto_zero_of_le (Valued.tendsto_zero_pow_of_v_lt_one hratio)
  intro n
  change (dvrPrime S).valuation L (x ^ n / (n.factorial : L)) ≤
    (dvrPrime S).valuation L ((x / (p : L)) ^ n)
  rw [map_div₀, map_pow, map_pow, map_div₀, div_pow]
  exact div_le_div_of_nonneg_left zero_le (pow_pos (localExpRadius_pos S L p) n)
    (dvr_valuation_factorial_lower S L p n)

/-- In a complete local fraction field, the actual exponential series converges
on v(x) < v(p), a positive domain supplied by the residue prime. -/
theorem localExp_summable (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    letI := dvrAdicValued S L
    CompleteSpace L → Summable (fun n : ℕ => x ^ n / (n.factorial : L)) := by
  let := dvrAdicValued S L
  intro hcomplete
  let : CompleteSpace L := hcomplete
  let : NonarchimedeanRing L := ((dvrPrime S).valuation L).subgroups_basis.nonarchimedean
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using localExpTerms_tendsto_zero S L p x hx

end LocalClassFieldTheory
