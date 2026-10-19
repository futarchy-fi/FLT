/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Basic.Lemmas
public import FltRegular.SmallNumbers.Eleven.FLT11
public import FltRegular.SmallNumbers.Five.FLT5
public import FltRegular.SmallNumbers.Seven.FLT7
public import FltRegular.SmallNumbers.Thirteen.FLT13

/-!
# The regular-prime boundary of the Frey argument

The four regular primes below seventeen are discharged by the vendored
class-number computations and `flt_regular`. No elliptic-curve input enters
this reduction. Exponents three and four are handled by `of_p_ge_5`.
-/

@[expose] public section

namespace FLT.Assembly

/-- All prime exponents between five and sixteen follow from regularity. -/
theorem flt_prime_lt_seventeen (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp17 : p < 17) : FermatLastTheoremFor p := by
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    have h : ∀ n ∈ Finset.Icc 5 16,
        n.Prime → n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by decide
    exact h p (by simp only [Finset.mem_Icc]; omega) hp
  rcases hcases with rfl | rfl | rfl | rfl
  · exact fermatLastTheoremFive
  · exact fermatLastTheoremSeven
  · exact fermatLastTheoremEleven
  · exact fermatLastTheoremThirteen

/-- Only prime exponents at least seventeen need the Frey-curve argument. -/
theorem flt_of_prime_ge_seventeen
    (hlarge : ∀ p, 17 ≤ p → p.Prime → FermatLastTheoremFor p) :
    FermatLastTheorem := by
  apply FermatLastTheorem.of_p_ge_5
  intro p hp5 hp
  by_cases hp17 : 17 ≤ p
  · exact hlarge p hp17 hp
  · exact flt_prime_lt_seventeen p hp hp5 (by omega)

end FLT.Assembly
