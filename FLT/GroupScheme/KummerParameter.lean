/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Removing a divisible valuation from a Kummer parameter

If `q` has the same valuation as `b ^ n`, then `q / b ^ n` is a unit of
the valuation ring. This does not require `n` to be invertible.
-/

@[expose] public section

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- A Kummer parameter whose valuation is an `n`-th power is an `n`-th power
times a unit of the valuation ring. -/
theorem exists_unit_factor_of_valuation_eq_pow (n : ℕ) (q b : Kˣ)
    (hval : A.valuation (q : K) = A.valuation (b : K) ^ n) :
    ∃ u : Aˣ, q = b ^ n * Units.map A.subtype.toMonoidHom u := by
  let x := q / b ^ n
  have hx : x ∈ A.unitGroup := by
    rw [A.mem_unitGroup_iff]
    simp only [x, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    rw [map_div₀, map_pow, hval]
    exact div_self (pow_ne_zero _ (A.valuation.ne_zero_iff.mpr b.ne_zero))
  let u := A.unitGroupMulEquiv ⟨x, hx⟩
  have hu : Units.map A.subtype.toMonoidHom u = x := by
    apply Units.ext
    rfl
  refine ⟨u, ?_⟩
  rw [hu]
  simp [x]

end ValuationSubring
