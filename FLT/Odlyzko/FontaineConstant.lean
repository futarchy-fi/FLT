/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Fontaine discriminant constant

Fontaine's discriminant bound (J.-M. Fontaine, *Il n'y a pas de variété abélienne sur `ℤ`*,
Invent. Math. **81** (1985), Théorème A together with its Corollaire) bounds the root
discriminant of the field cut out by a finite flat group scheme over `ℤ` with prescribed
ramification.  Applied at the prime `3` it yields two *different* local constants, according to
the ramification branch:

* **flat branch** — the wildly ramified, finite-flat case, which is the one relevant to the
  hardly-ramified mod-three representations attached to a Frey curve: the local factor is
  `3 ^ (3 / 2)`;
* **tame branch** — the local factor is `3 ^ (7 / 8)`.

The two constants are *not* interchangeable and have been conflated before, so both are recorded
here explicitly.  Our case is the **flat** one, `3 ^ (3 / 2)`, giving the root-discriminant bound

`|disc K| ^ (1 / n) ≤ 2 ^ (2 / 3) * 3 ^ (3 / 2) = 8.2483778…`

which sits just below the Odlyzko bound `8.25` available for totally complex fields of degree at
least `18`.  The margin is only about `0.0016`, so the elementary estimate below bounds each
factor to four decimal places:

* `2 ^ (2 / 3) ≤ 1.5875`, because `(2 ^ (2 / 3)) ^ 3 = 4 ≤ 1.5875 ^ 3 = 4.000748…`;
* `3 ^ (3 / 2) ≤ 5.1962`, because `(3 ^ (3 / 2)) ^ 2 = 27 ≤ 5.1962 ^ 2 = 27.000494…`,

whence the product is at most `1.5875 * 5.1962 = 8.24896…  < 8.25`.
-/

@[expose] public section

namespace Odlyzko

/-- `2 ^ (2 / 3) ≤ 1.5875`, certified by `(2 ^ (2 / 3)) ^ 3 = 4 ≤ 1.5875 ^ 3`. -/
theorem two_rpow_two_thirds_le : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 1.5875 := by
  have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = 4 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num) ?_
  rw [hcube]
  norm_num

/-- `3 ^ (3 / 2) ≤ 5.1962`, certified by `(3 ^ (3 / 2)) ^ 2 = 27 ≤ 5.1962 ^ 2`. -/
theorem three_rpow_three_halves_le : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 5.1962 := by
  have hsq : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = 27 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
  rw [hsq]
  norm_num

/-- The Fontaine constant of the **flat** branch at `3` is strictly below the Odlyzko bound
`8.25`: `2 ^ (2 / 3) * 3 ^ (3 / 2) = 8.2483778… < 8.25`. -/
theorem two_rpow_mul_three_rpow_lt :
    (2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ) < 8.25 := by
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  calc (2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ)
      ≤ 1.5875 * 5.1962 :=
        mul_le_mul two_rpow_two_thirds_le three_rpow_three_halves_le h3pos.le (by norm_num)
    _ < 8.25 := by norm_num

/-- Positivity of the Fontaine constant. -/
theorem two_rpow_mul_three_rpow_pos :
    (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ) :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)

end Odlyzko
