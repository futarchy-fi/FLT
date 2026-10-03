/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.NilpotentLogPower
public import Mathlib.Topology.Algebra.Polynomial

/-! # Finite logarithms commute with coefficient limits -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] [Algebra ℚ R]
variable [TopologicalSpace R] [IsTopologicalRing R]

/-- At a fixed quotient order all rational denominators are fixed coefficients. -/
theorem finiteNilpotentLog_continuous (r : ℕ) : Continuous (finiteNilpotentLog r : R → R) := by
  unfold finiteNilpotentLog
  fun_prop

/-- Integer log/power identities pass to simultaneous exponent and power limits. -/
theorem finiteNilpotentLog_pow_limit [T2Space R] {x y c : R} {r : ℕ}
    (hx : x ^ r = 0) (a : ℕ → ℕ)
    (ha : Filter.Tendsto (fun n ↦ (a n : R)) Filter.atTop (nhds c))
    (hp : Filter.Tendsto (fun n ↦ (1 + x) ^ a n) Filter.atTop (nhds y)) :
    finiteNilpotentLog r (y - 1) = c * finiteNilpotentLog r x := by
  have hlog := (finiteNilpotentLog_continuous (R := R) r).continuousAt.tendsto.comp
    (hp.sub_const 1)
  have hscalar := ha.mul_const (finiteNilpotentLog r x)
  have he : (fun n ↦ finiteNilpotentLog r ((1 + x) ^ a n - 1)) =
      (fun n ↦ (a n : R) * finiteNilpotentLog r x) := by
    funext n
    rw [finiteNilpotentLog_pow hx, nsmul_eq_mul]
  change Filter.Tendsto (fun n ↦ finiteNilpotentLog r ((1 + x) ^ a n - 1))
    Filter.atTop (nhds (finiteNilpotentLog r (y - 1))) at hlog
  rw [he] at hlog
  exact tendsto_nhds_unique hlog hscalar

end PadicHodgeTheory
