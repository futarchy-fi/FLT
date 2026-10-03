/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalExpLogInverse
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Multiplicativity of the actual local exponential

Unconditional nonarchimedean summability justifies the Cauchy product.
The binomial theorem identifies each antidiagonal coefficient, giving
exp(x+y)=exp(x)exp(y) on the proved convergence neighborhood.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [IsAdicComplete (maximalIdeal S) S] [CharZero L] in
/-- The exponential of zero is one. -/
theorem adicLocalExp_zero : adicLocalExp S L (0 : L) = 1 := by
  let := dvrAdicValued S L
  simp [adicLocalExp, zero_pow_eq, ite_div]

set_option maxHeartbeats 800000 in
-- Elaborating the Cauchy product and binomial coefficient casts exceeds the default limit.
/-- The exponential converts addition to multiplication on its convergence ball. -/
theorem adicLocalExp_add (x y : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L))
    (hy : (dvrPrime S).valuation L y < (dvrPrime S).valuation L (p : L)) :
    adicLocalExp S L (x + y) = adicLocalExp S L x * adicLocalExp S L y := by
  let := dvrAdicValued S L
  let : NonarchimedeanRing L := ((dvrPrime S).valuation L).subgroups_basis.nonarchimedean
  have hxs := adicLocalExp_summable S L p x hx
  have hys := adicLocalExp_summable S L p y hy
  unfold adicLocalExp
  rw [hxs.tsum_mul_tsum_eq_tsum_sum_antidiagonal hys (hxs.mul_of_nonarchimedean hys)]
  apply tsum_congr
  intro n
  rw [(Commute.all x y).add_pow', div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [← Nat.cast_smul_eq_nsmul L, smul_eq_mul, ← Finset.mem_antidiagonal.mp hkl,
    Nat.cast_add_choose]
  field_simp [Nat.factorial_ne_zero]

/-- Every exponential in the convergence ball is nonzero, with inverse exp(-x). -/
theorem adicLocalExp_mul_neg (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    adicLocalExp S L x * adicLocalExp S L (-x) = 1 := by
  rw [← adicLocalExp_add S L p x (-x) hx (by simpa using hx), add_neg_cancel,
    adicLocalExp_zero]

end LocalClassFieldTheory
