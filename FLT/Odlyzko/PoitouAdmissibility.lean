/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.TartarVariation

/-!
# Strong admissibility of the Gaussian Poitou regularization

Gaussian damping supplies the exponential decay margin in the strong Weil--Poitou test class.
The resulting approximants are admissible and form a concrete regularization of the weak scaled
Tartar test function.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ContDiff FourierTransform Topology

namespace Odlyzko

private theorem hasDerivAt_poitouGaussianCutoff (n : ℕ) (x : ℝ) :
    HasDerivAt (poitouGaussianCutoff n)
      (-2 * x / ((n : ℝ) + 1) * poitouGaussianCutoff n x) x := by
  have hinner : HasDerivAt (fun u : ℝ ↦ -u ^ 2 / ((n : ℝ) + 1))
      (-2 * x / ((n : ℝ) + 1)) x := by
    have h := ((hasDerivAt_id x).pow 2).neg.div_const ((n : ℝ) + 1)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u ↦ by
      simp only [id_eq, Pi.pow_apply, Pi.neg_apply]))
      |>.congr_deriv ?_
    norm_num
  unfold poitouGaussianCutoff
  refine hinner.exp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ ↦ rfl))
    |>.congr_deriv ?_
  ring

private theorem deriv_poitouGaussianCutoff (n : ℕ) :
    deriv (poitouGaussianCutoff n) = fun x : ℝ ↦
      -2 * x / ((n : ℝ) + 1) * poitouGaussianCutoff n x := by
  funext x
  exact (hasDerivAt_poitouGaussianCutoff n x).deriv

private theorem deriv_poitouGaussianCutoff_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖deriv (poitouGaussianCutoff n) x‖ ≤ C := by
  let c : ℝ := (n : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2 / c * Real.exp (c / 4), by positivity, fun x ↦ ?_⟩
  rw [deriv_poitouGaussianCutoff, Real.norm_eq_abs, abs_mul, abs_div, abs_mul,
    abs_of_pos hc, abs_of_pos (poitouGaussianCutoff_pos n x)]
  norm_num
  have hxexp : |x| ≤ Real.exp |x| := by
    calc
      |x| ≤ 1 + |x| := le_add_of_nonneg_left zero_le_one
      _ ≤ Real.exp |x| := by simpa [add_comm] using Real.add_one_le_exp |x|
  have hexpbound :
      Real.exp (-x ^ 2 / c + |x|) ≤ Real.exp (c / 4) := by
    apply Real.exp_le_exp.mpr
    have hsquare : 0 ≤ (2 * |x| - c) ^ 2 := sq_nonneg _
    have habssq : |x| ^ 2 = x ^ 2 := sq_abs x
    field_simp [hc.ne']
    nlinarith [hsquare]
  have hmul : |x| * poitouGaussianCutoff n x ≤ Real.exp (c / 4) := by
    calc
      |x| * poitouGaussianCutoff n x
          ≤ Real.exp |x| * poitouGaussianCutoff n x := by
            exact mul_le_mul_of_nonneg_right hxexp (poitouGaussianCutoff_pos n x).le
      _ = Real.exp (-x ^ 2 / c + |x|) := by
        rw [poitouGaussianCutoff]
        dsimp [c]
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (c / 4) := hexpbound
  dsimp [c] at hc ⊢
  calc
    2 * |x| / ((n : ℝ) + 1) * poitouGaussianCutoff n x =
        2 / ((n : ℝ) + 1) * (|x| * poitouGaussianCutoff n x) := by ring
    _ ≤ 2 / ((n : ℝ) + 1) * Real.exp (((n : ℝ) + 1) / 4) := by
      gcongr

theorem integrable_deriv_gaussianDampedNumerator {f : ℝ → ℝ}
    (hfdiff : Differentiable ℝ f) (hf : Integrable f)
    (hfderiv : Integrable (deriv f)) (n : ℕ) :
    Integrable (deriv (gaussianDampedNumerator f n)) := by
  have hcutoff_bdd : ∀ x : ℝ, ‖poitouGaussianCutoff n x‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (poitouGaussianCutoff_pos n x)]
    exact poitouGaussianCutoff_le_one n x
  have hfirst : Integrable (fun x : ℝ ↦
      deriv f x * poitouGaussianCutoff n x) :=
    hfderiv.mul_bdd (c := 1) (continuous_poitouGaussianCutoff n).aestronglyMeasurable
      (Filter.Eventually.of_forall hcutoff_bdd)
  obtain ⟨C, hC, hderiv_bdd⟩ := deriv_poitouGaussianCutoff_bounded n
  have hcutoff_deriv_cont : Continuous (deriv (poitouGaussianCutoff n)) := by
    rw [deriv_poitouGaussianCutoff]
    exact (by fun_prop : Continuous (fun x : ℝ ↦ -2 * x / ((n : ℝ) + 1))).mul
      (continuous_poitouGaussianCutoff n)
  have hsecond : Integrable (fun x : ℝ ↦
      f x * deriv (poitouGaussianCutoff n) x) :=
    hf.mul_bdd (c := C)
      hcutoff_deriv_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hderiv_bdd)
  have hsum := hfirst.add hsecond
  refine hsum.congr (Filter.Eventually.of_forall (fun x ↦ ?_))
  rw [show deriv (gaussianDampedNumerator f n) x =
      deriv f x * poitouGaussianCutoff n x +
        f x * deriv (poitouGaussianCutoff n) x by
    rw [deriv_poitouGaussianCutoff]
    unfold gaussianDampedNumerator
    exact ((hfdiff x).hasDerivAt.mul
      (hasDerivAt_poitouGaussianCutoff n x)).deriv]
  rfl

private theorem deriv_zero_of_even (F : ℝ → ℂ) (hF : Differentiable ℝ F)
    (hFeven : Function.Even F) : deriv F 0 = 0 := by
  have hderiv := (hF 0).hasDerivAt
  have hderivAtNeg : HasDerivAt F (deriv F 0) (-0) := by simpa using hderiv
  have hderivNeg := HasDerivAt.scomp (𝕜 := ℝ) 0 hderivAtNeg (hasDerivAt_neg 0)
  have hcomp : F ∘ Neg.neg = F := by
    funext x
    exact hFeven x
  rw [hcomp] at hderivNeg
  have hunique := hderiv.unique hderivNeg
  have hunique' : deriv F 0 = -deriv F 0 := by simpa using hunique
  exact CharZero.eq_neg_self_iff.mp hunique'

private theorem integrable_poitouKernel {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (poitouKernel f) := by
  have hweight_cont : Continuous (fun x : ℝ ↦ 1 / Real.cosh (x / 2)) :=
    continuous_const.div (Real.continuous_cosh.comp (continuous_id.div_const 2))
      (fun x ↦ (Real.cosh_pos _).ne')
  have hweight_bound : ∀ x : ℝ, ‖1 / Real.cosh (x / 2)‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_pos (Real.cosh_pos _)]
    exact (div_le_one (Real.cosh_pos _)).2 (by
      nlinarith [Real.cosh_sq (x / 2), sq_nonneg (Real.sinh (x / 2)),
        Real.cosh_pos (x / 2)])
  have hreal : Integrable (fun x : ℝ ↦ f x * (1 / Real.cosh (x / 2))) :=
    hf.mul_bdd (c := 1) hweight_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hweight_bound)
  have heq : (fun x : ℝ ↦ f x * (1 / Real.cosh (x / 2))) =
      fun x : ℝ ↦ f x / Real.cosh (x / 2) := by
    funext x
    ring
  rw [heq] at hreal
  exact hreal.ofReal

theorem boundedVariationOn_gaussianPoitouApproximant_diffQuot_scaledTartar
    {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    BoundedVariationOn
      (fun x : ℝ ↦
        (gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n 0 -
          gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n x) / x)
      (Set.Ici 0) := by
  let f := scaledNumerator tartarNumerator a
  let g := gaussianDampedNumerator f n
  let F := gaussianPoitouApproximant f n
  have hfcont : ContDiff ℝ ∞ f := contDiff_scaledTartarNumerator a
  have hgcont : ContDiff ℝ ∞ g := contDiff_gaussianDamped_scaledTartarNumerator a n
  have hFcont : ContDiff ℝ 2 F :=
    (contDiff_gaussianPoitouApproximant_scaledTartar a n).of_le (by simp)
  have hfint : Integrable f :=
    (integrable_comp_div_iff tartarNumerator ha).2 integrable_tartarNumerator
  have hgint : Integrable g := Integrable.gaussianDampedNumerator hfint n
  have hgderiv : Integrable (deriv g) :=
    integrable_deriv_gaussianDampedNumerator
      (hfcont.differentiable (by simp)) hfint (integrable_deriv_scaledTartarNumerator ha) n
  have hFint : Integrable F := integrable_poitouKernel hgint
  have hFderiv : Integrable (deriv F) :=
    integrable_deriv_poitouKernel (hgcont.differentiable (by simp)) hgint hgderiv
  have hfeven : Function.Even f := by
    intro x
    simpa only [f, scaledNumerator, neg_div] using tartarNumerator_even (x / a)
  have hFeven : Function.Even F :=
    poitouKernel_even (gaussianDampedNumerator_even hfeven n)
  exact boundedVariationOn_diffQuot_of_contDiff_two hFcont
    (deriv_zero_of_even F (hFcont.differentiable (by norm_num)) hFeven) hFint hFderiv

private noncomputable def gaussianAdmissibleWeight (n : ℕ) (x : ℝ) : ℝ :=
  poitouGaussianCutoff n x / Real.cosh (x / 2) * Real.exp ((3 / 4) * x)

private noncomputable def gaussianAdmissibleWeightDeriv (n : ℕ) (x : ℝ) : ℝ :=
  gaussianAdmissibleWeight n x *
    (-2 * x / ((n : ℝ) + 1) - Real.tanh (x / 2) / 2 + 3 / 4)

private theorem exp_neg_sq_add_mul_le (n : ℕ) (q x : ℝ) :
    Real.exp (-x ^ 2 / ((n : ℝ) + 1) + q * x) ≤
      Real.exp (((n : ℝ) + 1) * q ^ 2 / 4) := by
  apply Real.exp_le_exp.mpr
  have hc : 0 < (n : ℝ) + 1 := by positivity
  have hsquare : 0 ≤ (2 * x - ((n : ℝ) + 1) * q) ^ 2 := sq_nonneg _
  field_simp [hc.ne']
  nlinarith

private theorem gaussianAdmissibleWeight_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ gaussianAdmissibleWeight n x := by
  unfold gaussianAdmissibleWeight
  exact mul_nonneg
    (div_nonneg (poitouGaussianCutoff_pos n x).le (Real.cosh_pos _).le)
    (Real.exp_pos _).le

private theorem gaussianAdmissibleWeight_le_gaussian (n : ℕ) (x : ℝ) :
    gaussianAdmissibleWeight n x ≤
      Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * x) := by
  have hcosh : 1 ≤ Real.cosh (x / 2) := by
    nlinarith [Real.cosh_sq (x / 2), sq_nonneg (Real.sinh (x / 2)),
      Real.cosh_pos (x / 2)]
  unfold gaussianAdmissibleWeight
  have hinv : 1 / Real.cosh (x / 2) ≤ 1 :=
    (div_le_one (Real.cosh_pos _)).2 hcosh
  rw [div_eq_mul_inv, poitouGaussianCutoff, Real.exp_add]
  calc
    Real.exp (-x ^ 2 / ((n : ℝ) + 1)) * (Real.cosh (x / 2))⁻¹ *
        Real.exp (3 / 4 * x)
        ≤ Real.exp (-x ^ 2 / ((n : ℝ) + 1)) * 1 * Real.exp (3 / 4 * x) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinv)
              (Real.exp_pos _).le)
            (Real.exp_pos _).le
    _ = Real.exp (-x ^ 2 / ((n : ℝ) + 1)) * Real.exp (3 / 4 * x) := by ring

private theorem gaussianAdmissibleWeight_le (n : ℕ) (x : ℝ) :
    gaussianAdmissibleWeight n x ≤
      Real.exp (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ 2 / 4) := by
  calc
    gaussianAdmissibleWeight n x
        ≤ Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * x) :=
          gaussianAdmissibleWeight_le_gaussian n x
    _ ≤ _ := exp_neg_sq_add_mul_le n (3 / 4) x

private theorem mul_gaussianAdmissibleWeight_le (n : ℕ) (x : ℝ) :
    x * gaussianAdmissibleWeight n x ≤
      Real.exp (((n : ℝ) + 1) * (7 / 4 : ℝ) ^ 2 / 4) := by
  have hxexp : x ≤ Real.exp x := by
    calc
      x ≤ x + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ Real.exp x := Real.add_one_le_exp x
  calc
    x * gaussianAdmissibleWeight n x
        ≤ Real.exp x * gaussianAdmissibleWeight n x := by
          exact mul_le_mul_of_nonneg_right hxexp (gaussianAdmissibleWeight_nonneg n x)
    _ ≤ Real.exp x * Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * x) := by
      exact mul_le_mul_of_nonneg_left (gaussianAdmissibleWeight_le_gaussian n x)
        (Real.exp_pos _).le
    _ = Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (7 / 4) * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := exp_neg_sq_add_mul_le n (7 / 4) x

private theorem hasDerivAt_gaussianAdmissibleWeight (n : ℕ) (x : ℝ) :
    HasDerivAt (gaussianAdmissibleWeight n) (gaussianAdmissibleWeightDeriv n x) x := by
  have hcosh : HasDerivAt (fun u : ℝ ↦ Real.cosh (u / 2))
      (Real.sinh (x / 2) / 2) x := by
    simpa only [id_eq, div_eq_mul_inv, one_mul] using
      ((hasDerivAt_id x).div_const 2).cosh
  have hquot := (hasDerivAt_poitouGaussianCutoff n x).div hcosh
    (Real.cosh_pos (x / 2)).ne'
  have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp ((3 / 4) * u))
      ((3 / 4) * Real.exp ((3 / 4) * x)) x := by
    have hinner := (hasDerivAt_id x).const_mul (3 / 4)
    refine hinner.exp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u ↦ by simp only [id_eq]))
      |>.congr_deriv ?_
    simp only [id_eq]
    ring
  have h := hquot.mul hexp
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ ↦ rfl))
    |>.congr_deriv ?_
  rw [gaussianAdmissibleWeightDeriv, gaussianAdmissibleWeight,
    Real.tanh_eq_sinh_div_cosh]
  simp only [Pi.div_apply]
  field_simp [(Real.cosh_pos (x / 2)).ne']

private theorem gaussianAdmissibleWeightDeriv_boundedOn (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ici (0 : ℝ),
      ‖gaussianAdmissibleWeightDeriv n x‖ ≤ C := by
  let C₀ := Real.exp (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ 2 / 4)
  let C₁ := Real.exp (((n : ℝ) + 1) * (7 / 4 : ℝ) ^ 2 / 4)
  let c := (n : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2 / c * C₁ + 5 / 4 * C₀, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 ≤ x := hx
  have htanh : |Real.tanh (x / 2)| ≤ 1 := (Real.abs_tanh_lt_one _).le
  have hfactor :
      |-2 * x / c - Real.tanh (x / 2) / 2 + 3 / 4| ≤ 2 * x / c + 5 / 4 := by
    calc
      |-2 * x / c - Real.tanh (x / 2) / 2 + 3 / 4|
          ≤ |-2 * x / c| + |Real.tanh (x / 2) / 2| + |(3 / 4 : ℝ)| := by
            calc
              _ ≤ |-2 * x / c - Real.tanh (x / 2) / 2| + |(3 / 4 : ℝ)| :=
                abs_add_le _ _
              _ ≤ (|-2 * x / c| + |Real.tanh (x / 2) / 2|) +
                  |(3 / 4 : ℝ)| := by
                    gcongr
                    rw [sub_eq_add_neg]
                    simpa only [abs_neg] using
                      abs_add_le (-2 * x / c) (-(Real.tanh (x / 2) / 2))
      _ ≤ 2 * x / c + 5 / 4 := by
        rw [abs_div, abs_mul, abs_of_nonneg hx0, abs_of_pos hc, abs_div]
        norm_num
        nlinarith
  rw [gaussianAdmissibleWeightDeriv, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (gaussianAdmissibleWeight_nonneg n x)]
  calc
    gaussianAdmissibleWeight n x *
        |-2 * x / ((n : ℝ) + 1) - Real.tanh (x / 2) / 2 + 3 / 4|
        ≤ gaussianAdmissibleWeight n x * (2 * x / c + 5 / 4) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [c] using hfactor)
            (gaussianAdmissibleWeight_nonneg n x)
    _ = 2 / c * (x * gaussianAdmissibleWeight n x) +
        5 / 4 * gaussianAdmissibleWeight n x := by ring
    _ ≤ 2 / c * C₁ + 5 / 4 * C₀ := by
      gcongr
      · simpa only [C₁] using mul_gaussianAdmissibleWeight_le n x
      · simpa only [C₀] using gaussianAdmissibleWeight_le n x

private theorem continuous_gaussianAdmissibleWeight (n : ℕ) :
    Continuous (gaussianAdmissibleWeight n) := by
  unfold gaussianAdmissibleWeight
  exact ((continuous_poitouGaussianCutoff n).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2))
    (fun x ↦ (Real.cosh_pos _).ne')).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))

private noncomputable def gaussianAdmissibleWeightedDeriv
    (f : ℝ → ℝ) (n : ℕ) : ℝ → ℂ :=
  fun x ↦ ((deriv f x * gaussianAdmissibleWeight n x +
    f x * gaussianAdmissibleWeightDeriv n x : ℝ) : ℂ)

private theorem weighted_gaussianPoitouApproximant_eq
    (f : ℝ → ℝ) (n : ℕ) :
    (fun x : ℝ ↦ gaussianPoitouApproximant f n x *
      ((Real.exp ((1 / 2 + 1 / 4) * x) : ℝ) : ℂ)) =
      fun x : ℝ ↦ ((f x * gaussianAdmissibleWeight n x : ℝ) : ℂ) := by
  funext x
  simp only [gaussianPoitouApproximant, poitouKernel_apply, gaussianDampedNumerator,
    gaussianAdmissibleWeight]
  norm_num
  ring

private theorem integrableOn_weighted_gaussianPoitouApproximant
    {f : ℝ → ℝ} (hf : Integrable f) (n : ℕ) :
    IntegrableOn
      (fun x : ℝ ↦ gaussianPoitouApproximant f n x *
        ((Real.exp ((1 / 2 + 1 / 4) * x) : ℝ) : ℂ))
      (Set.Ici 0) := by
  have hweight_bound : ∀ x : ℝ,
      ‖gaussianAdmissibleWeight n x‖ ≤
        Real.exp (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ 2 / 4) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianAdmissibleWeight_nonneg n x)]
    exact gaussianAdmissibleWeight_le n x
  have hreal : IntegrableOn (fun x : ℝ ↦ f x * gaussianAdmissibleWeight n x)
      (Set.Ici 0) :=
    hf.integrableOn.mul_bdd
      (c := Real.exp (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ 2 / 4))
      (continuous_gaussianAdmissibleWeight n).aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hweight_bound)
  rw [weighted_gaussianPoitouApproximant_eq]
  exact hreal.ofReal

private theorem integrableOn_gaussianAdmissibleWeightedDeriv
    {f : ℝ → ℝ} (hf : Integrable f) (hfderiv : Integrable (deriv f)) (n : ℕ) :
    IntegrableOn (gaussianAdmissibleWeightedDeriv f n) (Set.Ici 0) := by
  let C₀ := Real.exp (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ 2 / 4)
  have hweight_bound : ∀ x : ℝ, ‖gaussianAdmissibleWeight n x‖ ≤ C₀ := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianAdmissibleWeight_nonneg n x)]
    simpa only [C₀] using gaussianAdmissibleWeight_le n x
  have hfirst : IntegrableOn (fun x : ℝ ↦
      deriv f x * gaussianAdmissibleWeight n x) (Set.Ici 0) :=
    hfderiv.integrableOn.mul_bdd (c := C₀)
      (continuous_gaussianAdmissibleWeight n).aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hweight_bound)
  obtain ⟨C₁, hC₁, hderiv_bound⟩ := gaussianAdmissibleWeightDeriv_boundedOn n
  have hderiv_cont : Continuous (gaussianAdmissibleWeightDeriv n) := by
    unfold gaussianAdmissibleWeightDeriv
    have htanh : Continuous Real.tanh := by
      rw [show Real.tanh = fun x ↦ Real.sinh x / Real.cosh x by
        funext x
        exact Real.tanh_eq_sinh_div_cosh x]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun x ↦ (Real.cosh_pos x).ne')
    exact (continuous_gaussianAdmissibleWeight n).mul
      ((((continuous_const.mul continuous_id).div_const ((n : ℝ) + 1)).sub
        ((htanh.comp (continuous_id.div_const 2)).div_const 2)).add continuous_const)
  have hsecond : IntegrableOn (fun x : ℝ ↦
      f x * gaussianAdmissibleWeightDeriv n x) (Set.Ici 0) :=
    hf.integrableOn.mul_bdd (c := C₁) hderiv_cont.aestronglyMeasurable.restrict
      ((ae_restrict_iff' measurableSet_Ici).2
        (Filter.Eventually.of_forall (fun x hx ↦ hderiv_bound x hx)))
  have hreal := hfirst.add hsecond
  exact hreal.ofReal

private theorem hasDerivAt_weighted_gaussianPoitouApproximant
    {f : ℝ → ℝ} (hfdiff : Differentiable ℝ f) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ gaussianPoitouApproximant f n x *
        ((Real.exp ((1 / 2 + 1 / 4) * x) : ℝ) : ℂ))
      (gaussianAdmissibleWeightedDeriv f n x) x := by
  rw [weighted_gaussianPoitouApproximant_eq]
  exact ((hfdiff x).hasDerivAt.mul (hasDerivAt_gaussianAdmissibleWeight n x)).ofReal_comp

theorem gaussianPoitouApproximant_isAdmissible_scaledTartar
    {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    DedekindResidue.IsAdmissibleTestFn
      (gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n) := by
  let f := scaledNumerator tartarNumerator a
  let F := gaussianPoitouApproximant f n
  have hfcont : ContDiff ℝ ∞ f := contDiff_scaledTartarNumerator a
  have hfint : Integrable f :=
    (integrable_comp_div_iff tartarNumerator ha).2 integrable_tartarNumerator
  have hfeven : Function.Even f := by
    intro x
    simpa only [f, scaledNumerator, neg_div] using tartarNumerator_even (x / a)
  have hFcont : Continuous F :=
    (contDiff_gaussianPoitouApproximant_scaledTartar a n).continuous
  refine ⟨poitouKernel_even (gaussianDampedNumerator_even hfeven n),
    ⟨1 / 4, by norm_num, ?_, ?_⟩, ?_, ?_⟩
  · apply DedekindResidue.boundedVariationOn_of_deriv_integrable Set.ordConnected_Ici
      (by
        rw [weighted_gaussianPoitouApproximant_eq]
        exact (Complex.ofRealCLM.continuous.comp
          (hfcont.continuous.mul (continuous_gaussianAdmissibleWeight n))).continuousOn)
    · rw [interior_Ici]
      intro x _
      exact hasDerivAt_weighted_gaussianPoitouApproximant
        (hfcont.differentiable (by simp)) n x
    · exact integrableOn_gaussianAdmissibleWeightedDeriv hfint
        (integrable_deriv_scaledTartarNumerator ha) n
  · exact integrableOn_weighted_gaussianPoitouApproximant hfint n
  · exact boundedVariationOn_gaussianPoitouApproximant_diffQuot_scaledTartar ha n
  · intro x
    refine ⟨F x, F x, ?_, ?_, by ring⟩
    · exact hFcont.continuousAt.mono_left inf_le_left
    · exact hFcont.continuousAt.mono_left inf_le_left

/-- The Gaussian family gives a concrete strong regularization of the weak scaled Tartar test. -/
noncomputable def scaledTartarPoitouRegularization {y : ℝ} (hy : 0 < y) :
    PoitouRegularization (scaledNumerator tartarNumerator (1 / √y)) where
  weak := scaledTartar_isPoitouTestFn_unconditional hy
  approximant := gaussianPoitouApproximant
    (scaledNumerator tartarNumerator (1 / √y))
  admissible n := gaussianPoitouApproximant_isAdmissible_scaledTartar
    (one_div_ne_zero (Real.sqrt_ne_zero'.2 hy)) n
  tendsto_kernel := tendsto_gaussianPoitouApproximant _

end Odlyzko
