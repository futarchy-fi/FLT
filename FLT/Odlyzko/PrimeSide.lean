/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Positivity of the prime side

The prime side of the Odlyzko explicit formula is a sum of terms
`log (N p) * (N p) ^ (-m / 2) * F (m * log (N p))`.  Each term is nonnegative when
`N p >= 2` and `F` is pointwise nonnegative.  Summability remains an explicit input supplied by
the admissibility condition at the analytic assembly seam.
-/

@[expose] public section

namespace Odlyzko

/-- A term in the prime side, indexed by a prime and a positive power. -/
noncomputable def primeTerm {P : Type*} (norm : P → ℝ) (F : ℝ → ℝ)
    (pm : P × ℕ+) : ℝ :=
  Real.log (norm pm.1) * (norm pm.1) ^ (-(pm.2 : ℝ) / 2) *
    F ((pm.2 : ℝ) * Real.log (norm pm.1))

/-- The prime side as one absolutely convergent series over primes and positive powers. -/
noncomputable def primeSide {P : Type*} (norm : P → ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑' pm : P × ℕ+, primeTerm norm F pm

theorem primeTerm_nonneg {P : Type*} (norm : P → ℝ) (F : ℝ → ℝ)
    (hnorm : ∀ p, 2 ≤ norm p) (hF : ∀ x, 0 ≤ F x) (pm : P × ℕ+) :
    0 ≤ primeTerm norm F pm := by
  unfold primeTerm
  have hnorm0 : 0 ≤ norm pm.1 := by linarith [hnorm pm.1]
  have hlog : 0 ≤ Real.log (norm pm.1) := Real.log_nonneg (by linarith [hnorm pm.1])
  exact mul_nonneg (mul_nonneg hlog (Real.rpow_nonneg hnorm0 _)) (hF _)

/-- P2: admissibility supplies `hsum`; positivity itself is termwise. -/
theorem primeSide_nonneg {P : Type*} (norm : P → ℝ) (F : ℝ → ℝ)
    (hnorm : ∀ p, 2 ≤ norm p) (hF : ∀ x, 0 ≤ F x)
    (_hsum : Summable (primeTerm norm F)) :
    0 ≤ primeSide norm F := by
  exact tsum_nonneg (primeTerm_nonneg norm F hnorm hF)

end Odlyzko
