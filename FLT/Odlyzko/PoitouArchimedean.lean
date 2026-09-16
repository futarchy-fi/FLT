/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Discard
public import FLT.Odlyzko.PoitouLargeY
public import FLT.Odlyzko.TartarLaplace
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Poitou's archimedean integral for the Tartar kernel

This file proves the exact archimedean identity used in Odlyzko's unconditional
discriminant bound.  At scale `y`, the sinh integral is `log 2 + Poitou.L1 y`;
consequently the constant-minus-integral term is
`γ + log (4π) - Poitou.L1 y`.
-/

@[expose] public section

open MeasureTheory Filter

namespace Odlyzko

/-- The archimedean sinh integral in the Weil--Poitou explicit formula. -/
noncomputable def poitouArchimedeanIntegral (F : ℝ → ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ),
    ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) * (F 0 - F x)

namespace Poitou

/-- On the power-series disc, the large-parameter representation agrees with `L1`. -/
theorem L1large_eq_L1 {y : ℝ} (hy : 0 < y) (hy4 : y < 1 / 4) :
    L1large y = L1 y := by
  rw [L1large, L1]
  have hsum := L1_summable hy hy4
  rw [hsum.tsum_eq_zero_add, L1term_zero, Lclosed_eq_L hy hy4]

private noncomputable def basePrimitive (x : ℝ) : ℝ :=
  Real.log 2 + Real.log (1 + Real.exp (-x)) -
    2 * Real.log (1 + Real.exp (-(x / 2)))

private noncomputable def baseDeriv (x : ℝ) : ℝ :=
  -Real.exp (-x) / (1 + Real.exp (-x)) +
    Real.exp (-(x / 2)) / (1 + Real.exp (-(x / 2)))

private theorem hasDerivAt_basePrimitive (x : ℝ) :
    HasDerivAt basePrimitive (baseDeriv x) x := by
  have h₁ : HasDerivAt (fun x : ℝ ↦ 1 + Real.exp (-x))
      (-Real.exp (-x)) x := by
    have he : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-Real.exp (-x)) x := by
      convert ((hasDerivAt_id x).neg.exp) using 1
      · ext y
        rfl
      · simp only [Pi.neg_apply, id_eq]
        ring
    exact he.const_add 1
  have h₂ : HasDerivAt (fun x : ℝ ↦ 1 + Real.exp (-(x / 2)))
      (-(Real.exp (-(x / 2)) / 2)) x := by
    have hx : HasDerivAt (fun x : ℝ ↦ -(x / 2)) (-(1 / 2)) x :=
      ((hasDerivAt_id x).div_const 2).neg
    have he : HasDerivAt (fun x : ℝ ↦ Real.exp (-(x / 2)))
        (-(Real.exp (-(x / 2)) / 2)) x := by
      convert hx.exp using 1
      ring
    exact he.const_add 1
  have hlog₁ := h₁.log (by positivity)
  have hlog₂ := h₂.log (by positivity)
  have h := ((hasDerivAt_const x (Real.log 2)).add hlog₁).sub
    (hlog₂.const_mul 2)
  unfold basePrimitive baseDeriv
  have hfun :
      (((fun _ : ℝ ↦ Real.log 2) + fun y ↦ Real.log (1 + Real.exp (-y))) -
        fun y ↦ 2 * Real.log (1 + Real.exp (-(y / 2)))) =
      fun y ↦ Real.log 2 + Real.log (1 + Real.exp (-y)) -
        2 * Real.log (1 + Real.exp (-(y / 2))) := by
    funext y
    rfl
  rw [hfun] at h
  apply h.congr_deriv
  field_simp
  ring

private theorem baseDeriv_eq (x : ℝ) (hx : 0 < x) :
    baseDeriv x = 1 / (2 * Real.sinh (x / 2)) - 1 / Real.sinh x := by
  rw [baseDeriv]
  have h1 : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  let r := Real.exp (-(x / 2))
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hsinhhalf : Real.sinh (x / 2) = (1 - r ^ 2) / (2 * r) := by
    rw [Real.sinh_eq]
    dsimp [r] at h3 ⊢
    field_simp
    nlinarith
  have h3sq := congrArg (fun t : ℝ ↦ t ^ 2) h3
  have hsinh : Real.sinh x = (1 - r ^ 4) / (2 * r ^ 2) := by
    rw [Real.sinh_eq, h1, h2]
    dsimp [r] at h3sq ⊢
    field_simp
    ring_nf at h3sq ⊢
    nlinarith
  rw [h1, hsinhhalf, hsinh]
  have hr2 : 0 < 1 - r ^ 2 :=
    sub_pos.mpr (pow_lt_one₀ hr.le hr1 (by norm_num))
  have hr4 : 0 < 1 - r ^ 4 :=
    sub_pos.mpr (pow_lt_one₀ hr.le hr1 (by norm_num))
  dsimp [r] at hr hr1 hr2 hr4 ⊢
  field_simp [hr.ne', hr2.ne', hr4.ne']
  ring

private theorem tendsto_basePrimitive :
    Tendsto basePrimitive atTop (nhds (Real.log 2)) := by
  have h₁ : Tendsto (fun x : ℝ ↦ Real.exp (-x)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have h₂ : Tendsto (fun x : ℝ ↦ Real.exp (-(x / 2))) atTop (nhds 0) := by
    convert h₁.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)) using 1
    ext x
    congr 1
  have hlog₁ : Tendsto (fun x : ℝ ↦ Real.log (1 + Real.exp (-x))) atTop
      (nhds 0) := by
    convert (h₁.const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    norm_num
  have hlog₂ : Tendsto (fun x : ℝ ↦ Real.log (1 + Real.exp (-(x / 2)))) atTop
      (nhds 0) := by
    convert (h₂.const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    norm_num
  change Tendsto
    (fun x : ℝ ↦ Real.log 2 + Real.log (1 + Real.exp (-x)) -
      2 * Real.log (1 + Real.exp (-(x / 2)))) _ _
  convert (tendsto_const_nhds.add hlog₁).sub (tendsto_const_nhds.mul hlog₂) using 1
  norm_num

private theorem baseDeriv_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ baseDeriv x := by
  have hsq : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hr1 : Real.exp (-(x / 2)) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  rw [baseDeriv, hsq, neg_div, neg_add_eq_sub, sub_nonneg]
  rw [div_le_div_iff₀ (by positivity : 0 < 1 + Real.exp (-(x / 2)) ^ 2)
    (by positivity : 0 < 1 + Real.exp (-(x / 2)))]
  nlinarith [Real.exp_pos (-(x / 2))]

private theorem integral_baseDeriv :
    ∫ x in Set.Ioi (0 : ℝ), baseDeriv x = Real.log 2 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x _ ↦ hasDerivAt_basePrimitive x)
    (fun x hx ↦ baseDeriv_nonneg x (Set.mem_Ioi.mp hx)) tendsto_basePrimitive
  rw [show basePrimitive 0 = 0 by norm_num [basePrimitive]; ring] at h
  simpa using h

private theorem integrableOn_baseDeriv :
    IntegrableOn baseDeriv (Set.Ioi 0) := by
  have h₁ : IntegrableOn (fun x : ℝ ↦ Real.exp (-x) / (1 + Real.exp (-x)))
      (Set.Ioi 0) := by
    have hdom := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
    refine hdom.mono' (Continuous.aestronglyMeasurable (by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        positivity)).restrict ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [show (-1 : ℝ) * x = -x by ring]
    exact div_le_self (Real.exp_pos _).le (by linarith [Real.exp_pos (-x)])
  have h₂ : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(x / 2)) / (1 + Real.exp (-(x / 2))))
      (Set.Ioi 0) := by
    have hdom := integrableOn_exp_mul_Ioi (a := (-(1 / 2) : ℝ)) (by norm_num) 0
    refine hdom.mono' (Continuous.aestronglyMeasurable (by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        positivity)).restrict ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [show -(1 / 2 : ℝ) * x = -(x / 2) by ring]
    exact div_le_self (Real.exp_pos _).le (by linarith [Real.exp_pos (-(x / 2))])
  apply (h₁.neg.add h₂).congr_fun _ measurableSet_Ioi
  intro x _
  change -(Real.exp (-x) / (1 + Real.exp (-x))) +
    Real.exp (-(x / 2)) / (1 + Real.exp (-(x / 2))) = baseDeriv x
  unfold baseDeriv
  ring

private noncomputable def laplaceRow (y : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  2 * (1 - tartarNumerator (x * √y)) * Real.exp (-x) * Real.exp (-2 * x) ^ m

private theorem laplaceRow_eq (y : ℝ) (m : ℕ) (x : ℝ) :
    laplaceRow y m x =
      2 * (1 - tartarNumerator (x * √y)) * Real.exp (-(2 * (m : ℝ) + 1) * x) := by
  rw [laplaceRow, ← Real.exp_nat_mul]
  have h : Real.exp (-x) * Real.exp ((m : ℝ) * (-2 * x)) =
      Real.exp (-(2 * (m : ℝ) + 1) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    2 * (1 - tartarNumerator (x * √y)) * Real.exp (-x) *
        Real.exp ((m : ℝ) * (-2 * x)) =
      2 * (1 - tartarNumerator (x * √y)) *
        (Real.exp (-x) * Real.exp ((m : ℝ) * (-2 * x))) := by ring
    _ = _ := by rw [h]

private theorem laplaceRow_nonneg (y : ℝ) (m : ℕ) (x : ℝ) :
    0 ≤ laplaceRow y m x := by
  unfold laplaceRow
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (sub_nonneg.mpr (tartarNumerator_le_one _))) (Real.exp_pos _).le) (by positivity)

private theorem integrableOn_laplaceRow (y : ℝ) (m : ℕ) :
    IntegrableOn (laplaceRow y m) (Set.Ioi 0) := by
  let q : ℝ := 2 * (m : ℝ) + 1
  have hq : 0 < q := by dsimp [q]; positivity
  have hdom : IntegrableOn (fun x : ℝ ↦ 2 * Real.exp (-q * x)) (Set.Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -q) (by linarith) 0
    simpa only [IntegrableOn, neg_mul] using h.const_mul 2
  have hnum : Continuous (fun x : ℝ ↦ tartarNumerator (x * √y)) :=
    continuous_tartarNumerator.comp (continuous_id.mul continuous_const)
  refine hdom.mono' (by unfold laplaceRow; fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (laplaceRow_nonneg y m x), laplaceRow_eq]
  have hf := tartarNumerator_nonneg (x * √y)
  have hexp := Real.exp_pos (-(2 * (m : ℝ) + 1) * x)
  dsimp [q]
  nlinarith

private theorem integral_laplaceRow {y : ℝ} (hy : 0 < y) (hy4 : y < 1 / 4)
    (m : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), laplaceRow y m x = L1term y m := by
  let q : ℝ := 2 * (m : ℝ) + 1
  have hq : 0 < q := by dsimp [q]; positivity
  have hq2 : 1 ≤ q ^ 2 := by
    dsimp [q]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hscaled : y / q ^ 2 < 1 / 4 := by
    have hle : y / q ^ 2 ≤ y := by
      rw [div_le_iff₀ (sq_pos_of_pos hq)]
      nlinarith
    exact hle.trans_lt hy4
  rw [show (∫ x in Set.Ioi (0 : ℝ), laplaceRow y m x) =
      2 * ∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y)) * Real.exp (-q * x) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    rw [laplaceRow_eq]
    dsimp [q]
    ring]
  rw [tartarNumerator_laplace_eq_L hy hq hscaled]
  rfl

private noncomputable def largeArchimedeanValue (y : ℝ) : ℕ → ℝ
  | 0 => Real.log 2
  | 1 => Lclosed y
  | m + 2 => L1term y (m + 1)

private theorem integral_laplaceRow_large {y : ℝ} (hy : 0 < y) (hy9 : y < 9 / 4)
    (m : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), laplaceRow y m x = largeArchimedeanValue y (m + 1) := by
  let q : ℝ := 2 * (m : ℝ) + 1
  have hq : 0 < q := by dsimp [q]; positivity
  rw [show (∫ x in Set.Ioi (0 : ℝ), laplaceRow y m x) =
      2 * ∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y)) * Real.exp (-q * x) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    rw [laplaceRow_eq]
    dsimp [q]
    ring]
  cases m with
  | zero =>
      simpa [q, largeArchimedeanValue] using
        tartarNumerator_laplace_eq_Lclosed hy hq
  | succ m =>
      have hscaled : y / q ^ 2 < 1 / 4 := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hq2 : 9 ≤ q ^ 2 := by dsimp [q]; push_cast; nlinarith
        rw [div_lt_iff₀ (sq_pos_of_pos hq)]
        nlinarith
      rw [tartarNumerator_laplace_eq_L hy hq hscaled]
      simp only [largeArchimedeanValue, L1term]
      dsimp [q]

private theorem summable_largeArchimedeanValue {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) : Summable (largeArchimedeanValue y) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [largeArchimedeanValue, Nat.add_assoc, Nat.reduceAdd] using
    L1large_tail_summable hy hy9

private theorem tsum_largeArchimedeanValue {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) :
    ∑' m, largeArchimedeanValue y m = Real.log 2 + L1large y := by
  have hsum := summable_largeArchimedeanValue hy hy9
  rw [hsum.tsum_eq_zero_add]
  have htail : Summable (fun m => largeArchimedeanValue y (m + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  rw [htail.tsum_eq_zero_add]
  simp only [largeArchimedeanValue, L1large]

private theorem summable_laplaceRow (y : ℝ) {x : ℝ} (hx : 0 < x) :
    Summable (fun m : ℕ ↦ laplaceRow y m x) := by
  have hr0 : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 * x) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left
    (2 * (1 - tartarNumerator (x * √y)) * Real.exp (-x))

private theorem laplaceRows_sum {y x : ℝ} (hx : 0 < x) :
    ∑' m : ℕ, laplaceRow y m x =
      (1 - tartarNumerator (x * √y)) / Real.sinh x := by
  have hr0 : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 * x) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hsum := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (2 * (1 - tartarNumerator (x * √y)) * Real.exp (-x))
  simp only [laplaceRow]
  rw [HasSum.tsum_eq hsum]
  rw [Real.sinh_eq]
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hexp2 : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hexp2]
  have hr : 0 < Real.exp (-x) := Real.exp_pos _
  have hrlt : Real.exp (-x) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hr2 : 0 < 1 - Real.exp (-x) ^ 2 :=
    sub_pos.mpr (pow_lt_one₀ hr.le hrlt (by norm_num))
  have hden : 0 < Real.exp x - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hkernel : 2 * Real.exp (-x) * (1 - Real.exp (-x) ^ 2)⁻¹ =
      1 / ((Real.exp x - Real.exp (-x)) / 2) := by
    field_simp [hr2.ne', hden.ne']
    nlinarith
  calc
    2 * (1 - tartarNumerator (x * √y)) * Real.exp (-x) *
        (1 - Real.exp (-x) ^ 2)⁻¹ =
      (1 - tartarNumerator (x * √y)) *
        (2 * Real.exp (-x) * (1 - Real.exp (-x) ^ 2)⁻¹) := by ring
    _ = (1 - tartarNumerator (x * √y)) *
        (1 / ((Real.exp x - Real.exp (-x)) / 2)) := by rw [hkernel]
    _ = _ := by ring

private noncomputable def archimedeanRow (y : ℝ) : ℕ → ℝ → ℝ
  | 0 => baseDeriv
  | m + 1 => laplaceRow y m

private theorem archimedeanRows_sum (y : ℝ) {x : ℝ} (hx : 0 < x) :
    ∑' m : ℕ, archimedeanRow y m x =
      (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2)) := by
  have hs : Summable (fun m : ℕ ↦ archimedeanRow y m x) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [archimedeanRow, Nat.add_eq, Nat.add_zero] using summable_laplaceRow y hx
  rw [hs.tsum_eq_zero_add]
  simp only [archimedeanRow]
  rw [laplaceRows_sum hx, baseDeriv_eq x hx]
  have hsh : Real.sinh (x / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
  have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hxsh : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    rw [← Real.sinh_two_mul]
    congr 1
    ring
  rw [hxsh]
  field_simp [hsh, hch]
  ring

/-- Odlyzko's archimedean identity in the large-parameter range used by the
degree-eighteen certificate. -/
theorem integral_scaledTartar_div_sinh_eq_log_two_add_L1large {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) :
    (∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2))) =
      Real.log 2 + L1large y := by
  have hint : ∀ m : ℕ, Integrable (archimedeanRow y m)
      (volume.restrict (Set.Ioi 0)) := by
    intro m
    cases m with
    | zero => exact integrableOn_baseDeriv
    | succ m => exact integrableOn_laplaceRow y m
  have hvalue : (fun m : ℕ => ∫ x in Set.Ioi (0 : ℝ), archimedeanRow y m x) =
      largeArchimedeanValue y := by
    funext m
    cases m with
    | zero => exact integral_baseDeriv
    | succ m => exact integral_laplaceRow_large hy hy9 m
  have hnorm : (fun m : ℕ => ∫ x in Set.Ioi (0 : ℝ), ‖archimedeanRow y m x‖) =
      largeArchimedeanValue y := by
    funext m
    cases m with
    | zero =>
        simp only [archimedeanRow]
        rw [show (∫ x in Set.Ioi (0 : ℝ), ‖baseDeriv x‖) =
            ∫ x in Set.Ioi (0 : ℝ), baseDeriv x by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          change ‖baseDeriv x‖ = baseDeriv x
          rw [Real.norm_eq_abs, abs_of_nonneg
            (baseDeriv_nonneg x (Set.mem_Ioi.mp hx))], integral_baseDeriv]
        rfl
    | succ m =>
        simp only [archimedeanRow]
        rw [show (∫ x in Set.Ioi (0 : ℝ), ‖laplaceRow y m x‖) =
            ∫ x in Set.Ioi (0 : ℝ), laplaceRow y m x by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change ‖laplaceRow y m x‖ = laplaceRow y m x
          rw [Real.norm_eq_abs, abs_of_nonneg (laplaceRow_nonneg y m x)]]
        exact integral_laplaceRow_large hy hy9 m
  have hsum : Summable (fun m : ℕ =>
      ∫ x in Set.Ioi (0 : ℝ), ‖archimedeanRow y m x‖) := by
    rw [hnorm]
    exact summable_largeArchimedeanValue hy hy9
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  calc
    (∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2))) =
      ∫ x in Set.Ioi (0 : ℝ), ∑' m : ℕ, archimedeanRow y m x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact (archimedeanRows_sum y (Set.mem_Ioi.mp hx)).symm
    _ = ∑' m : ℕ, ∫ x in Set.Ioi (0 : ℝ), archimedeanRow y m x := hswap.symm
    _ = ∑' m, largeArchimedeanValue y m := by rw [hvalue]
    _ = Real.log 2 + L1large y := tsum_largeArchimedeanValue hy hy9

/-- Odlyzko's exact archimedean identity for the scaled Tartar numerator. -/
theorem integral_scaledTartar_div_sinh_eq_log_two_add_L1 {y : ℝ}
    (hy : 0 < y) (hy4 : y < 1 / 4) :
    (∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2))) =
      Real.log 2 + L1 y := by
  have hint : ∀ m : ℕ, Integrable (archimedeanRow y m)
      (volume.restrict (Set.Ioi 0)) := by
    intro m
    cases m with
    | zero => exact integrableOn_baseDeriv
    | succ m => exact integrableOn_laplaceRow y m
  have hnorm : (fun m : ℕ ↦ ∫ x in Set.Ioi (0 : ℝ), ‖archimedeanRow y m x‖) =
      fun m ↦ match m with
        | 0 => Real.log 2
        | k + 1 => L1term y k := by
    funext m
    cases m with
    | zero =>
        simp only [archimedeanRow]
        rw [show (∫ x in Set.Ioi (0 : ℝ), ‖baseDeriv x‖) =
            ∫ x in Set.Ioi (0 : ℝ), baseDeriv x by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          change ‖baseDeriv x‖ = baseDeriv x
          rw [Real.norm_eq_abs, abs_of_nonneg
            (baseDeriv_nonneg x (Set.mem_Ioi.mp hx))], integral_baseDeriv]
    | succ m =>
        simp only [archimedeanRow]
        rw [show (∫ x in Set.Ioi (0 : ℝ), ‖laplaceRow y m x‖) =
            ∫ x in Set.Ioi (0 : ℝ), laplaceRow y m x by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change ‖laplaceRow y m x‖ = laplaceRow y m x
          rw [Real.norm_eq_abs, abs_of_nonneg (laplaceRow_nonneg y m x)]]
        exact integral_laplaceRow hy hy4 m
  have hsum : Summable (fun m : ℕ ↦
      ∫ x in Set.Ioi (0 : ℝ), ‖archimedeanRow y m x‖) := by
    rw [hnorm]
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_eq, Nat.add_zero] using L1_summable hy hy4
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hleft : (∑' m : ℕ, ∫ x in Set.Ioi (0 : ℝ), archimedeanRow y m x) =
      Real.log 2 + L1 y := by
    rw [show (fun m : ℕ ↦ ∫ x in Set.Ioi (0 : ℝ), archimedeanRow y m x) =
        fun m ↦ match m with
          | 0 => Real.log 2
          | k + 1 => L1term y k by
      funext m
      cases m with
      | zero => exact integral_baseDeriv
      | succ m => exact integral_laplaceRow hy hy4 m]
    have hv : Summable (fun m ↦ match m with
        | 0 => Real.log 2
        | k + 1 => L1term y k) := by
      rw [← hnorm]
      exact hsum
    rw [hv.tsum_eq_zero_add]
    simp only [L1]
  calc
    (∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2))) =
      ∫ x in Set.Ioi (0 : ℝ), ∑' m : ℕ, archimedeanRow y m x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact (archimedeanRows_sum y (Set.mem_Ioi.mp hx)).symm
    _ = ∑' m : ℕ, ∫ x in Set.Ioi (0 : ℝ), archimedeanRow y m x := hswap.symm
    _ = Real.log 2 + L1 y := hleft

/-- The limiting scaled-Tartar archimedean integrand is integrable throughout the
large-parameter range. -/
theorem integrableOn_scaledTartar_archimedeanIntegrand_large {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) :
    IntegrableOn
      (fun x : ℝ ↦ (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2)))
      (Set.Ioi 0) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  have hint : ∀ m : ℕ, Integrable (archimedeanRow y m) μ := by
    intro m
    cases m with
    | zero => exact integrableOn_baseDeriv
    | succ m => exact integrableOn_laplaceRow y m
  have hnorm : (fun m : ℕ ↦ ∫ x, ‖archimedeanRow y m x‖ ∂μ) =
      largeArchimedeanValue y := by
    funext m
    cases m with
    | zero =>
        simp only [archimedeanRow]
        rw [show (∫ x, ‖baseDeriv x‖ ∂μ) = ∫ x, baseDeriv x ∂μ by
          apply integral_congr_ae
          refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
          exact Filter.Eventually.of_forall fun x hx ↦ by
            change ‖baseDeriv x‖ = baseDeriv x
            rw [Real.norm_eq_abs, abs_of_nonneg (baseDeriv_nonneg x hx)]]
        exact integral_baseDeriv
    | succ m =>
        simp only [archimedeanRow]
        rw [show (∫ x, ‖laplaceRow y m x‖ ∂μ) = ∫ x, laplaceRow y m x ∂μ by
          apply integral_congr_ae
          filter_upwards with x
          rw [Real.norm_eq_abs, abs_of_nonneg (laplaceRow_nonneg y m x)]]
        exact integral_laplaceRow_large hy hy9 m
  have hsum : Summable (fun m : ℕ ↦ ∫ x, ‖archimedeanRow y m x‖ ∂μ) := by
    rw [hnorm]
    exact summable_largeArchimedeanValue hy hy9
  have hlin : (∑' m : ℕ, ∫⁻ x, ‖archimedeanRow y m x‖ₑ ∂μ) < ⊤ := by
    have heach (m : ℕ) : ∫⁻ x, ‖archimedeanRow y m x‖ₑ ∂μ =
        ‖∫ x, ‖archimedeanRow y m x‖ ∂μ‖ₑ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hint m),
        Real.enorm_eq_ofReal (integral_nonneg (fun x ↦ norm_nonneg _))]
    rw [funext heach, lt_top_iff_ne_top]
    exact tsum_enorm_ne_top_iff_summable_norm.2 hsum.norm
  have hnum : Continuous (fun x : ℝ ↦ tartarNumerator (x * √y)) :=
    continuous_tartarNumerator.comp (continuous_id.mul continuous_const)
  have htop : Continuous
      (fun x : ℝ ↦ 1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) :=
    continuous_const.sub (hnum.div (Real.continuous_cosh.comp (continuous_id.div_const 2))
      (fun x ↦ (Real.cosh_pos _).ne'))
  have hcontinuous : ContinuousOn
      (fun x : ℝ ↦ (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2))) (Set.Ioi 0) := by
    apply ContinuousOn.div htop.continuousOn (by fun_prop)
    intro x hx
    exact mul_ne_zero (by norm_num)
      (Real.sinh_pos_iff.mpr (by linarith [Set.mem_Ioi.mp hx])).ne'
  refine ⟨hcontinuous.aestronglyMeasurable measurableSet_Ioi, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x, ‖(1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2))‖ₑ ∂μ) =
      ∫⁻ x, ‖∑' m : ℕ, archimedeanRow y m x‖ₑ ∂μ := by
        apply lintegral_congr_ae
        refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
        exact Filter.Eventually.of_forall fun x hx ↦ by
          change ‖(1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))‖ₑ = ‖∑' m : ℕ, archimedeanRow y m x‖ₑ
          rw [archimedeanRows_sum y hx]
    _ ≤ ∫⁻ x, ∑' m : ℕ, ‖archimedeanRow y m x‖ₑ ∂μ :=
      lintegral_mono fun x ↦ enorm_tsum_le_tsum_enorm
    _ = ∑' m : ℕ, ∫⁻ x, ‖archimedeanRow y m x‖ₑ ∂μ := by
      rw [lintegral_tsum]
      intro m
      exact (hint m).aestronglyMeasurable.enorm
    _ < ⊤ := hlin

/-- The limiting scaled-Tartar archimedean integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_scaledTartar_archimedeanIntegrand {y : ℝ}
    (hy : 0 < y) (hy4 : y < 1 / 4) :
    IntegrableOn
      (fun x : ℝ ↦ (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2)))
      (Set.Ioi 0) :=
  integrableOn_scaledTartar_archimedeanIntegrand_large hy (hy4.trans (by norm_num))

private noncomputable def gaussianArchimedeanError (x : ℝ) : ℝ :=
  (1 - Real.exp (-x ^ 2)) / Real.sinh x

private theorem gaussianArchimedeanError_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ gaussianArchimedeanError x := by
  unfold gaussianArchimedeanError
  exact div_nonneg (sub_nonneg.mpr (by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg x))))
    (Real.sinh_pos_iff.mpr hx).le

private theorem integrableOn_gaussianArchimedeanError :
    IntegrableOn gaussianArchimedeanError (Set.Ioi 0) := by
  have hcontinuous : ContinuousOn gaussianArchimedeanError (Set.Ioi 0) := by
    unfold gaussianArchimedeanError
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact (Real.sinh_pos_iff.mpr (Set.mem_Ioi.mp hx)).ne'
  have hlocalDom : IntegrableOn (fun x : ℝ ↦ x) (Set.Ioc 0 1) :=
    continuous_id.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hlocal : IntegrableOn gaussianArchimedeanError (Set.Ioc 0 1) := by
    refine hlocalDom.mono'
      ((hcontinuous.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    exact Filter.Eventually.of_forall fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianArchimedeanError_nonneg hx.1)]
      unfold gaussianArchimedeanError
      rw [div_le_iff₀ (Real.sinh_pos_iff.mpr hx.1)]
      have hnum := Real.one_sub_le_exp_neg (x ^ 2)
      have hsinh := (Real.self_le_sinh_iff (x := x)).mpr hx.1.le
      nlinarith [mul_le_mul_of_nonneg_left hsinh hx.1.le]
  have htailDom : IntegrableOn (fun x : ℝ ↦ 4 * Real.exp (-x)) (Set.Ioi 1) := by
    have h := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1
    change Integrable (fun x : ℝ ↦ 4 * Real.exp (-x)) (volume.restrict (Set.Ioi 1))
    simpa only [neg_one_mul] using h.const_mul 4
  have htail : IntegrableOn gaussianArchimedeanError (Set.Ioi 1) := by
    refine htailDom.mono'
      ((hcontinuous.mono (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun x hx ↦ by
      have hx1 : 1 < x := Set.mem_Ioi.mp hx
      have hx0 : 0 < x := lt_trans (by norm_num) hx1
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianArchimedeanError_nonneg hx0)]
      have hrpos : 0 < Real.exp (-x) := Real.exp_pos _
      have hrhalf : Real.exp (-x) < 1 / 2 := by
        have hneg : -x < (-1 : ℝ) := by linarith
        exact (Real.exp_lt_exp.mpr hneg).trans Real.exp_neg_one_lt_half
      have hexp : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have hsinh : Real.sinh x = (1 - Real.exp (-x) ^ 2) /
          (2 * Real.exp (-x)) := by
        rw [Real.sinh_eq]
        field_simp
        nlinarith
      have hden : 0 < 1 - Real.exp (-x) ^ 2 := by nlinarith
      have hkernel : 1 / Real.sinh x ≤ 4 * Real.exp (-x) := by
        rw [hsinh]
        field_simp [hrpos.ne', hden.ne']
        nlinarith
      unfold gaussianArchimedeanError
      calc
        (1 - Real.exp (-x ^ 2)) / Real.sinh x ≤ 1 / Real.sinh x := by
          apply div_le_div_of_nonneg_right _ (Real.sinh_pos_iff.mpr hx0).le
          linarith [Real.exp_pos (-x ^ 2)]
        _ ≤ 4 * Real.exp (-x) := hkernel
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hlocal.union htail

/-- The explicit-formula sinh integral in the large-parameter range. -/
theorem poitouArchimedeanIntegral_scaledTartar_eq_large {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) :
    poitouArchimedeanIntegral (scaledPoitouKernel tartarNumerator (1 / √y)) =
      ((Real.log 2 + L1large y : ℝ) : ℂ) := by
  rw [poitouArchimedeanIntegral]
  calc
    (∫ x in Set.Ioi (0 : ℝ),
        ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) *
          (scaledPoitouKernel tartarNumerator (1 / √y) 0 -
            scaledPoitouKernel tartarNumerator (1 / √y) x)) =
      ∫ x in Set.Ioi (0 : ℝ),
        (((1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2)) : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        change ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) *
            (scaledPoitouKernel tartarNumerator (1 / √y) 0 -
              scaledPoitouKernel tartarNumerator (1 / √y) x) = _
        rw [scaledPoitouKernel_tartar_eq y 0 hy,
          scaledPoitouKernel_tartar_eq y x hy]
        norm_num
        ring
    _ = ((∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2)) : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [integral_scaledTartar_div_sinh_eq_log_two_add_L1large hy hy9]

/-- The explicit-formula sinh integral of the scaled Tartar kernel is `log 2 + L1 y`. -/
theorem poitouArchimedeanIntegral_scaledTartar_eq {y : ℝ}
    (hy : 0 < y) (hy4 : y < 1 / 4) :
    poitouArchimedeanIntegral (scaledPoitouKernel tartarNumerator (1 / √y)) =
      ((Real.log 2 + L1 y : ℝ) : ℂ) := by
  rw [poitouArchimedeanIntegral_scaledTartar_eq_large hy (hy4.trans (by norm_num)),
    L1large_eq_L1 hy hy4]

private theorem poitouGaussianCutoff_zero_le (n : ℕ) (x : ℝ) :
    poitouGaussianCutoff 0 x ≤ poitouGaussianCutoff n x := by
  unfold poitouGaussianCutoff
  apply Real.exp_le_exp.mpr
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : 1 ≤ (n : ℝ) + 1 := by linarith
  have hdiv := div_le_self (sq_nonneg x) hn
  norm_num
  simpa only [neg_div] using neg_le_neg hdiv

/-- The archimedean integrals of the Gaussian regularization converge throughout
the large-parameter range. -/
theorem tendsto_poitouArchimedeanIntegral_gaussian_scaledTartar_large {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) :
    Tendsto
      (fun n ↦ poitouArchimedeanIntegral
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n))
      atTop (nhds ((Real.log 2 + L1large y : ℝ) : ℂ)) := by
  let f := scaledNumerator tartarNumerator (1 / √y)
  let F : ℕ → ℝ → ℂ := gaussianPoitouApproximant f
  let G : ℕ → ℝ → ℂ := fun n x ↦
    ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) * (F n 0 - F n x)
  let Glim : ℝ → ℂ := fun x ↦
    ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) *
      (scaledPoitouKernel tartarNumerator (1 / √y) 0 -
        scaledPoitouKernel tartarNumerator (1 / √y) x)
  let B : ℝ → ℝ := fun x ↦
    (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2)) + gaussianArchimedeanError x
  have hB : IntegrableOn B (Set.Ioi 0) :=
    (integrableOn_scaledTartar_archimedeanIntegrand_large hy hy9).add
      integrableOn_gaussianArchimedeanError
  have hform (n : ℕ) (x : ℝ) (hx : 0 < x) :
      G n x = (((1 - tartarNumerator (x * √y) * poitouGaussianCutoff n x /
        Real.cosh (x / 2)) / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) := by
    have hfzero : f 0 = 1 := by simp [f, scaledNumerator]
    change ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) *
      (gaussianPoitouApproximant f n 0 - gaussianPoitouApproximant f n x) = _
    simp only [gaussianPoitouApproximant, poitouKernel_apply,
      gaussianDampedNumerator_zero hfzero]
    dsimp [f]
    rw [gaussianDampedNumerator, scaledNumerator_tartar_eq y x hy]
    norm_num [Real.cosh_zero]
    ring
  have hdecomp (n : ℕ) (x : ℝ) (hx : 0 < x) :
      (1 - tartarNumerator (x * √y) * poitouGaussianCutoff n x /
          Real.cosh (x / 2)) / (2 * Real.sinh (x / 2)) =
        (1 - tartarNumerator (x * √y) / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2)) +
          tartarNumerator (x * √y) *
            ((1 - poitouGaussianCutoff n x) / Real.sinh x) := by
    have hsh : Real.sinh (x / 2) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (by linarith)).ne'
    have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
    have hxsh : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
      rw [← Real.sinh_two_mul]
      congr 1
      ring
    rw [hxsh]
    field_simp [hsh, hch]
    ring
  have hbound (n : ℕ) : ∀ᵐ x ∂volume.restrict (Set.Ioi 0), ‖G n x‖ ≤ B x := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun x hx ↦ by
      have hx0 := Set.mem_Ioi.mp hx
      rw [hform n x hx0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by
          apply div_nonneg
          · apply sub_nonneg.mpr
            apply (div_le_one (Real.cosh_pos _)).2
            have hmul : tartarNumerator (x * √y) * poitouGaussianCutoff n x ≤ 1 := by
              calc
                tartarNumerator (x * √y) * poitouGaussianCutoff n x ≤
                    1 * poitouGaussianCutoff n x :=
                  mul_le_mul_of_nonneg_right (tartarNumerator_le_one _)
                    (poitouGaussianCutoff_pos n x).le
                _ ≤ 1 := by simpa using poitouGaussianCutoff_le_one n x
            exact hmul.trans (Real.one_le_cosh _)
          · positivity), hdecomp n x hx0]
      have hcutNonneg : 0 ≤ 1 - poitouGaussianCutoff n x :=
        sub_nonneg.mpr (poitouGaussianCutoff_le_one n x)
      have herrorNonneg : 0 ≤ (1 - poitouGaussianCutoff n x) / Real.sinh x :=
        div_nonneg hcutNonneg (Real.sinh_pos_iff.mpr hx0).le
      have herror : (1 - poitouGaussianCutoff n x) / Real.sinh x ≤
          gaussianArchimedeanError x := by
        have hzero : poitouGaussianCutoff 0 x = Real.exp (-x ^ 2) := by
          norm_num [poitouGaussianCutoff]
        unfold gaussianArchimedeanError
        rw [← hzero]
        exact div_le_div_of_nonneg_right
          (sub_le_sub_left (poitouGaussianCutoff_zero_le n x) 1)
          (Real.sinh_pos_iff.mpr hx0).le
      have hf := tartarNumerator_le_one (x * √y)
      have hf0 := tartarNumerator_nonneg (x * √y)
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_left herror hf0]
  have hmeas (n : ℕ) : AEStronglyMeasurable (G n)
      (volume.restrict (Set.Ioi 0)) := by
    have hscalarReal : ContinuousOn
        (fun x : ℝ ↦ 1 / (2 * Real.sinh (x / 2))) (Set.Ioi 0) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx
      exact mul_ne_zero (by norm_num)
        (Real.sinh_pos_iff.mpr (by linarith [Set.mem_Ioi.mp hx])).ne'
    have hscalar : ContinuousOn
        (fun x : ℝ ↦ ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn hscalarReal
    have hFcont : Continuous (F n) := by
      dsimp [F, f]
      exact (contDiff_gaussianPoitouApproximant_scaledTartar (1 / √y) n).continuous
    exact (hscalar.mul (continuous_const.sub hFcont).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  have hlim : ∀ᵐ x ∂volume.restrict (Set.Ioi 0),
      Tendsto (fun n ↦ G n x) atTop (nhds (Glim x)) := by
    filter_upwards with x
    dsimp [G, Glim, F, f]
    exact tendsto_const_nhds.mul
      ((tendsto_scaledTartar_gaussianPoitouApproximant y 0).sub
        (tendsto_scaledTartar_gaussianPoitouApproximant y x))
  have h := tendsto_integral_of_dominated_convergence B hmeas hB hbound hlim
  change Tendsto
    (fun n ↦ poitouArchimedeanIntegral
      (gaussianPoitouApproximant
        (scaledNumerator tartarNumerator (1 / √y)) n)) atTop _
  rw [← poitouArchimedeanIntegral_scaledTartar_eq_large hy hy9]
  simpa only [poitouArchimedeanIntegral, G, Glim, F, f] using h

/-- The archimedean integrals of the Gaussian regularization converge to Poitou's
power-series value. -/
theorem tendsto_poitouArchimedeanIntegral_gaussian_scaledTartar {y : ℝ}
    (hy : 0 < y) (hy4 : y < 1 / 4) :
    Tendsto
      (fun n ↦ poitouArchimedeanIntegral
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n))
      atTop (nhds ((Real.log 2 + L1 y : ℝ) : ℂ)) := by
  simpa only [L1large_eq_L1 hy hy4] using
    tendsto_poitouArchimedeanIntegral_gaussian_scaledTartar_large
      hy (hy4.trans (by norm_num))

/-- The scaled Tartar kernel gives Poitou's large-parameter archimedean lower term. -/
theorem archimedeanLowerTerm_scaledTartar_eq_large {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) :
    archimedeanLowerTerm
        (poitouArchimedeanIntegral (scaledPoitouKernel tartarNumerator (1 / √y))) =
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - L1large y := by
  rw [archimedeanLowerTerm, poitouArchimedeanIntegral_scaledTartar_eq_large hy hy9]
  simp only [Complex.ofReal_re]
  rw [show (8 : ℝ) * Real.pi = 2 * (4 * Real.pi) by ring,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 4 * Real.pi ≠ 0)]
  ring

/-- The scaled Tartar kernel gives Poitou's closed archimedean lower term. -/
theorem archimedeanLowerTerm_scaledTartar_eq {y : ℝ}
    (hy : 0 < y) (hy4 : y < 1 / 4) :
    archimedeanLowerTerm
        (poitouArchimedeanIntegral (scaledPoitouKernel tartarNumerator (1 / √y))) =
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - L1 y := by
  rw [archimedeanLowerTerm, poitouArchimedeanIntegral_scaledTartar_eq hy hy4]
  simp only [Complex.ofReal_re]
  rw [show (8 : ℝ) * Real.pi = 2 * (4 * Real.pi) by ring,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 4 * Real.pi ≠ 0)]
  ring

/-- The Gaussian archimedean lower terms converge to the large-parameter value. -/
theorem tendsto_archimedeanLowerTerm_gaussian_scaledTartar_large {y : ℝ}
    (hy : 0 < y) (hy9 : y < 9 / 4) :
    Tendsto
      (fun n ↦ archimedeanLowerTerm
        (poitouArchimedeanIntegral
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n)))
      atTop (nhds
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - L1large y)) := by
  have hcont : Continuous archimedeanLowerTerm := by
    unfold archimedeanLowerTerm
    fun_prop
  have h := hcont.continuousAt.tendsto.comp
    (tendsto_poitouArchimedeanIntegral_gaussian_scaledTartar_large hy hy9)
  have hlimit : archimedeanLowerTerm ((Real.log 2 + L1large y : ℝ) : ℂ) =
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - L1large y := by
    rw [← poitouArchimedeanIntegral_scaledTartar_eq_large hy hy9,
      archimedeanLowerTerm_scaledTartar_eq_large hy hy9]
  change Tendsto
    (fun n ↦ archimedeanLowerTerm
      (poitouArchimedeanIntegral
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n))) atTop _ at h
  rw [hlimit] at h
  exact h

/-- The archimedean lower terms of the Gaussian approximants converge to
Poitou's closed Tartar-kernel value. -/
theorem tendsto_archimedeanLowerTerm_gaussian_scaledTartar {y : ℝ}
    (hy : 0 < y) (hy4 : y < 1 / 4) :
    Tendsto
      (fun n ↦ archimedeanLowerTerm
        (poitouArchimedeanIntegral
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n)))
      atTop (nhds
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - L1 y)) := by
  have hcont : Continuous archimedeanLowerTerm := by
    unfold archimedeanLowerTerm
    fun_prop
  have h := hcont.continuousAt.tendsto.comp
    (tendsto_poitouArchimedeanIntegral_gaussian_scaledTartar hy hy4)
  have hlimit : archimedeanLowerTerm ((Real.log 2 + L1 y : ℝ) : ℂ) =
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - L1 y := by
    rw [← poitouArchimedeanIntegral_scaledTartar_eq hy hy4,
      archimedeanLowerTerm_scaledTartar_eq hy hy4]
  change Tendsto
    (fun n ↦ archimedeanLowerTerm
      (poitouArchimedeanIntegral
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n))) atTop _ at h
  rw [hlimit] at h
  exact h

end Poitou
end Odlyzko
