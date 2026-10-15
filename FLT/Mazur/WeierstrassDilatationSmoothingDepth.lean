/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationSmoothingDeepCongruence

/-!
# Exact arithmetic depth of the computed terminal smoothing

Deeper divisibility of the original linear coefficients controls the entire
smoothing correction. Below that correction order, the depth is exactly that of b6.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b3 b4 b6 : R)
  (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6

/-- Order-k linear coefficients force the exact smoothing correction into order 2k. -/
theorem terminalSmoothing_sub_mem_pow (k : ℕ) (h3k : b3 ∈ I ^ k) (h4k : b4 ∈ I ^ k) :
    c - b6 ∈ I ^ (2 * k) := by
  simpa only [← pow_mul, Nat.mul_comm k 2] using
    terminalSmoothing_sub_mem_ideal_sq b3 b4 b6 r (I ^ k) h3k h4k W I hI hrI ha h4 h6

/-- Every order through 2k is detected by the retained original constant, even beyond I². -/
theorem terminalSmoothing_mem_pow_iff (k n : ℕ) (h3k : b3 ∈ I ^ k)
    (h4k : b4 ∈ I ^ k) (hn : n ≤ 2 * k) : c ∈ I ^ n ↔ b6 ∈ I ^ n := by
  have hc : c - b6 ∈ I ^ n := Ideal.pow_le_pow_right hn
    (terminalSmoothing_sub_mem_pow W b3 b4 b6 r I hI hrI ha h4 h6 k h3k h4k)
  constructor
  · intro h
    have hh := (I ^ n).sub_mem h hc
    simpa only [sub_sub_cancel] using hh
  · intro h
    have hh := (I ^ n).add_mem hc h
    simpa only [sub_add_cancel] using hh

/-- The computed smoothing has the exact depth of b6 when its next order precedes 2k. -/
theorem terminalSmoothing_exact_depth (k n : ℕ) (h3k : b3 ∈ I ^ k)
    (h4k : b4 ∈ I ^ k) (hn : n + 1 ≤ 2 * k)
    (h6n : b6 ∈ I ^ n) (h6next : b6 ∉ I ^ (n + 1)) :
    c ∈ I ^ n ∧ c ∉ I ^ (n + 1) := by
  constructor
  · exact (terminalSmoothing_mem_pow_iff W b3 b4 b6 r I hI hrI ha h4 h6
      k n h3k h4k (by omega)).mpr h6n
  · intro hc
    exact h6next ((terminalSmoothing_mem_pow_iff W b3 b4 b6 r I hI hrI ha h4 h6
      k (n + 1) h3k h4k hn).mp hc)

end FLT.Mazur.WeierstrassDilatation
