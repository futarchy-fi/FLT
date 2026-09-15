/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Discard
public import FLT.Odlyzko.TartarLaplace

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

/-- The explicit-formula sinh integral of the scaled Tartar kernel is `log 2 + L1 y`. -/
theorem poitouArchimedeanIntegral_scaledTartar_eq {y : ℝ}
    (hy : 0 < y) (hy4 : y < 1 / 4) :
    poitouArchimedeanIntegral (scaledPoitouKernel tartarNumerator (1 / √y)) =
      ((Real.log 2 + L1 y : ℝ) : ℂ) := by
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
    _ = _ := by rw [integral_scaledTartar_div_sinh_eq_log_two_add_L1 hy hy4]

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

end Poitou
end Odlyzko
