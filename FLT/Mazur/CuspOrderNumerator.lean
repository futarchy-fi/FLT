/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith

/-!
# A lower bound for the cusp-order numerator

For every natural number `p ≥ 17`, the numerator of `(p - 1) / 12` is at least
two in absolute value. This is the numerical inequality used in Mazur,
*Modular curves and the Eisenstein ideal* (1977), III (3.1) and §5 Step 3, p. 160.
It requires no primality assumption and does not identify the order of a cusp.
-/

public section

namespace FLT.Mazur

/-- The numerator of `(p - 1) / 12` is at least two when `p ≥ 17`. -/
theorem cuspOrderNumerator_ge_two (p : ℕ) (hp : 17 ≤ p) :
    2 ≤ ((((p - 1 : ℕ) : ℚ) / 12).num.natAbs) := by
  let q : ℚ := ((p - 1 : ℕ) : ℚ) / 12
  have hq : 1 < q := by
    dsimp [q]
    apply (lt_div_iff₀ (by norm_num)).mpr
    exact_mod_cast (show 12 < p - 1 by omega)
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have he : (q.num : ℚ) = q * q.den :=
    (div_eq_iff (show (q.den : ℚ) ≠ 0 by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  have hn : (1 : ℚ) < q.num := by nlinarith
  have hn' : (1 : ℤ) < q.num := by exact_mod_cast hn
  change 2 ≤ q.num.natAbs
  omega

end FLT.Mazur
