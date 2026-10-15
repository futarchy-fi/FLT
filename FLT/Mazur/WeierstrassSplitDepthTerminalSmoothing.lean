/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalNode
public import FLT.Mazur.WeierstrassDilatationSmoothingDepth
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassSplitDepthArithmeticNodeOpen
public import FLT.Mazur.PolygonArithmeticIdealPowers

/-!
# Exact terminal smoothing depth forced by the original split-node data

At divided depth k strictly before the middle, the computed smoothing has
exact depth n-2k in every quotient that sees that order. No smoothing depth is assumed.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n k : ℕ}
  (D : SplitNodeDepth W π n) (d : Data W π k) (hpos : 0 < k) (hk : 2 * k < n) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- The computed smoothing of the whole terminal node, built from the original split datum. -/
def splitDepthTerminalSmoothing : Q :=
  WeierstrassDilatation.arithmeticTerminalSmoothing π m W (π ^ k) d.b3 d.b4 d.b6
    D.a₁_unit (dvd_pow_self π (Nat.ne_of_gt hpos)) (splitDepth_a2_dvd D)
    (splitDepth_linear_dvd D d (Nat.le_of_lt hk)).2 (splitDepth_constant_dvd D d hk)
local notation "c" => splitDepthTerminalSmoothing D d hpos hk m

/-- Original split depth forces the exact computed smoothing depth at every visible order. -/
theorem splitDepthTerminalSmoothing_exact_depth (hm : n - 2 * k ≤ m) :
    c ∈ J ^ (n - 2 * k) ∧ c ∉ J ^ (n - 2 * k + 1) := by
  have hl := divided_linear_deep_mem D d (by omega)
  have hc := divided_constant_exact_depth D d (Nat.le_of_lt hk)
  have hc₀ : d.b6 ∈ ideal R π ^ (n - 2 * k) := by
    simpa only [D.maximalIdeal_eq, ideal] using hc.1
  have hc₁ : d.b6 ∉ ideal R π ^ (n - 2 * k + 1) := by
    simpa only [D.maximalIdeal_eq, ideal] using hc.2
  have hq := coefficient_exact_parameterIdeal_depth π m (n - 2 * k) hm hc₀ hc₁
  unfold splitDepthTerminalSmoothing WeierstrassDilatation.arithmeticTerminalSmoothing
  apply WeierstrassDilatation.terminalSmoothing_exact_depth (k := n + 1 - k)
  · apply coefficient_mem_parameterIdeal_pow π m
    simpa only [D.maximalIdeal_eq, ideal] using hl.1
  · apply coefficient_mem_parameterIdeal_pow π m
    simpa only [D.maximalIdeal_eq, ideal] using hl.2
  · omega
  · exact hq.1
  · exact hq.2

/-- The original terminal smoothing is nonzero at every quotient that sees its exact depth. -/
theorem splitDepthTerminalSmoothing_ne_zero (hm : n - 2 * k ≤ m) : c ≠ 0 := by
  intro he
  have hn := (splitDepthTerminalSmoothing_exact_depth D d hpos hk m hm).2
  rw [he] at hn
  exact hn ((J ^ (n - 2 * k + 1)).zero_mem)

end FLT.Mazur.WeierstrassDividedDepth
