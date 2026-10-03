/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Comparison of sequences in a valued field

A sequence dominated in valuation by a sequence tending to zero also
tends to zero, directly from the valuation neighborhood basis.
-/

@[expose] public section

namespace LocalClassFieldTheory

open Filter
open scoped Topology WithZero

variable {L : Type*} [Field L] [Valued L ℤᵐ⁰]

/-- Valuation domination transfers convergence to zero. -/
theorem valuation_tendsto_zero_of_le {a b : ℕ → L}
    (hb : Tendsto b atTop (𝓝 0)) (h : ∀ n, Valued.v (a n) ≤ Valued.v (b n)) :
    Tendsto a atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero L ℤᵐ⁰).tendsto_right_iff] at hb ⊢
  intro γ hγ
  filter_upwards [hb γ hγ] with n hn
  exact lt_of_le_of_lt (Valued.v.restrict_le_iff.mpr (h n)) hn

end LocalClassFieldTheory
