/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalLogConvergence
public import FLT.LocalClassFieldTheory.ValuationUniformSeries

/-!
# Uniform local logarithm convergence

For every a with v(a) < v(p), the logarithm tails on v(x) ≤ v(a)
are bounded by v(a (a/p)^N), uniformly in x. Thus the partial sums
converge uniformly on these closed principal-unit neighborhoods.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Filter IsLocalRing
open scoped Topology WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- The local logarithm, expressed as a convergent sum near 1. -/
def adicLocalLog (u : L) : L :=
  letI := dvrAdicValued S L
  ∑' n, localLogTerm (u - 1) n

/-- The actual logarithm tail admits a uniform geometric valuation bound. -/
theorem localLog_tail_le (a x : L)
    (ha : (dvrPrime S).valuation L a < (dvrPrime S).valuation L (p : L))
    (hx : (dvrPrime S).valuation L x ≤ (dvrPrime S).valuation L a) (N : ℕ) :
    (dvrPrime S).valuation L
      (adicLocalLog S L (1 + x) - ∑ n ∈ Finset.range N, localLogTerm x n) ≤
      (dvrPrime S).valuation L (a * (a / (p : L)) ^ N) := by
  let := dvrAdicValued S L
  have hq : Valued.v (a / (p : L)) < 1 := by
    change (dvrPrime S).valuation L _ < 1
    rwa [map_div₀, div_lt_one₀ (localExpRadius_pos S L p)]
  change Valued.v (adicLocalLog S L (1 + x) -
    ∑ n ∈ Finset.range N, localLogTerm x n) ≤ Valued.v (a * (a / (p : L)) ^ N)
  simpa only [adicLocalLog, add_sub_cancel_left] using valuation_series_tail_le
    (localLog_summable S L p x (lt_of_le_of_lt hx ha)) a (a / (p : L)) hq.le
    (localLogTerm_le S L p x a hx) N

/-- Logarithm partial sums converge uniformly on every smaller closed ball. -/
theorem localLog_tendstoUniformlyOn (a : L)
    (ha : (dvrPrime S).valuation L a < (dvrPrime S).valuation L (p : L)) :
    letI := dvrAdicValued S L
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, localLogTerm x n)
      (fun x => adicLocalLog S L (1 + x)) atTop
      {x | (dvrPrime S).valuation L x ≤ (dvrPrime S).valuation L a} := by
  let := dvrAdicValued S L
  have hq : Valued.v (a / (p : L)) < 1 := by
    change (dvrPrime S).valuation L _ < 1
    rwa [map_div₀, div_lt_one₀ (localExpRadius_pos S L p)]
  simpa only [adicLocalLog, add_sub_cancel_left] using valuation_series_tendstoUniformlyOn
    (U := {x : L | (dvrPrime S).valuation L x ≤ (dvrPrime S).valuation L a})
    (fun x hx => localLog_summable S L p x (lt_of_le_of_lt hx ha)) a (a / (p : L)) hq
    (fun x hx => localLogTerm_le S L p x a hx)

end LocalClassFieldTheory
