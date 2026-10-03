/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ValuationSeriesComparison
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.UniformConvergence

/-!
# Uniform geometric tail estimates in valued fields

Closed valuation balls contain convergent sums of their elements. A geometric
term bound therefore controls every tail and gives uniform convergence of
the partial sums on any set where the same bound applies.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Filter
open scoped Topology WithZero

variable {L : Type*} [Field L] [Valued L ℤᵐ⁰]

/-- A convergent sum inherits any common closed-ball bound on its terms. -/
theorem valuation_tsum_le {ι : Type*} {f : ι → L} (hf : Summable f)
    (a : L) (ha : ∀ i, Valued.v (f i) ≤ Valued.v a) :
    Valued.v (∑' i, f i) ≤ Valued.v a := by
  apply Valued.v.restrict_le_iff.mp
  apply (Valued.isClosed_closedBall L (Valued.v.restrict a)).mem_of_tendsto hf.hasSum
  exact Eventually.of_forall fun s =>
    Valued.v.restrict.map_sum_le fun i _ => Valued.v.restrict_le_iff.mpr (ha i)

/-- A geometric bound on terms yields the same bound on the tail after N terms. -/
theorem valuation_series_tail_le {f : ℕ → L} (hf : Summable f) (a q : L)
    (hq : Valued.v q ≤ 1) (h : ∀ n, Valued.v (f n) ≤ Valued.v (a * q ^ n)) (N : ℕ) :
    Valued.v ((∑' n, f n) - ∑ n ∈ Finset.range N, f n) ≤ Valued.v (a * q ^ N) := by
  rw [← hf.sum_add_tsum_nat_add N, add_sub_cancel_left]
  apply valuation_tsum_le (f := fun n => f (n + N))
    ((summable_nat_add_iff N).mpr hf) (a * q ^ N)
  intro n
  apply (h (n + N)).trans
  simp only [map_mul, map_pow]
  exact mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hq (Nat.le_add_left N n))

/-- Geometrically bounded series converge uniformly wherever their bound is uniform. -/
theorem valuation_series_tendstoUniformlyOn {X : Type*} {U : Set X} {f : ℕ → X → L}
    (hf : ∀ x ∈ U, Summable (fun n => f n x)) (a q : L) (hq : Valued.v q < 1)
    (h : ∀ x ∈ U, ∀ n, Valued.v (f n x) ≤ Valued.v (a * q ^ n)) :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, f n x)
      (fun x => ∑' n, f n x) atTop U := by
  rw [(Valued.hasBasis_uniformity L ℤᵐ⁰).tendstoUniformlyOn_iff_of_uniformity]
  have ht : Tendsto (fun n : ℕ => a * q ^ n) atTop (𝓝 (0 : L)) := by
    simpa using (Valued.tendsto_zero_pow_of_v_lt_one hq).const_mul a
  rw [(Valued.hasBasis_nhds_zero L ℤᵐ⁰).tendsto_right_iff] at ht
  intro γ hγ
  filter_upwards [ht γ hγ] with N hN x hx
  change Valued.v.restrict ((∑ n ∈ Finset.range N, f n x) - ∑' n, f n x) < γ.val
  rw [Valuation.map_sub_swap]
  exact (Valued.v.restrict_le_iff.mpr
    (valuation_series_tail_le (hf x hx) a q hq.le (h x hx) N)).trans_lt hN

end LocalClassFieldTheory
