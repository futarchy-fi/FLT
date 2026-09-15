/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.AINTLIB.DedekindResidue.ExplicitFormula.WeilAssembly
public import FLT.Odlyzko.PoitouArchimedean
public import FLT.Odlyzko.PoitouBoundary
public import FLT.Odlyzko.ZeroDivisorSymmetry

/-!
# Weil--Poitou adapter for Gaussian Tartar approximants

This file connects the window limit produced by AINTLIB's Weil explicit formula to the
totally complex interface used by the Odlyzko discard argument.  Admissibility supplies
the analytic control of `paperPhi`; Poitou positivity makes every bounded zero window
nonnegative; and the Gaussian cutoff makes the prime side summable and nonnegative.
-/

@[expose] public section

open Complex Filter MeasureTheory
open scoped FourierTransform Topology

namespace Odlyzko

open Module NumberField

theorem paperPhi_diffContOnCl_of_isAdmissible {F : ℝ → ℂ}
    (hF : DedekindResidue.IsAdmissibleTestFn F) :
    DiffContOnCl ℂ (DedekindResidue.paperPhi F)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  obtain ⟨ε, hε, _, hint⟩ := hF.bv_integrable_exp
  constructor
  · intro z hz
    exact (DedekindResidue.hasDerivAt_paperPhi hF hε hint
      (by linarith [hz.1]) (by linarith [hz.2])).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz' : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
      rw [Complex.HadamardThreeLines.verticalClosedStrip,
        ← closure_Ioo zero_ne_one, ← closure_preimage_re]
      exact hz
    exact (DedekindResidue.hasDerivAt_paperPhi hF hε hint
      (by linarith [hz'.1]) (by linarith [hz'.2])).continuousAt.continuousWithinAt

theorem paperPhi_bddAbove_of_isAdmissible {F : ℝ → ℂ}
    (hF : DedekindResidue.IsAdmissibleTestFn F) :
    BddAbove ((norm ∘ DedekindResidue.paperPhi F) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  obtain ⟨ε, hε, _, hint⟩ := hF.bv_integrable_exp
  let g : ℝ → ℝ := fun x ↦ ‖F x‖ *
    (Real.exp ((1 / 2 + ε) * x) + Real.exp (-((1 / 2 + ε) * x)))
  have hg : Integrable g := DedekindResidue.integrable_admissible_majorant hF hε hint
  refine ⟨∫ x, g x, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hkernel : Integrable (fun x : ℝ ↦
      F x * Complex.exp ((z - 1 / 2) * x)) :=
    DedekindResidue.integrable_paperPhi_kernel hF hint
      (by linarith [hz.1]) (by linarith [hz.2])
  rw [Function.comp_apply, DedekindResidue.paperPhi]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono hkernel.norm hg
  intro x
  change ‖F x * Complex.exp ((z - 1 / 2) * (x : ℂ))‖ ≤ g x
  dsimp [g]
  rw [norm_mul, Complex.norm_exp]
  have hre : ((z - 1 / 2) * (x : ℂ)).re = (z.re - 1 / 2) * x := by
    simp [Complex.mul_re]
  rw [hre]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rcases le_or_gt 0 x with hx | hx
  · calc
      Real.exp ((z.re - 1 / 2) * x) ≤ Real.exp ((1 / 2 + ε) * x) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hz.2]
      _ ≤ Real.exp ((1 / 2 + ε) * x) + Real.exp (-((1 / 2 + ε) * x)) := by
        exact le_add_of_nonneg_right (Real.exp_pos _).le
  · calc
      Real.exp ((z.re - 1 / 2) * x) ≤ Real.exp (-((1 / 2 + ε) * x)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hz.1]
      _ ≤ Real.exp ((1 / 2 + ε) * x) + Real.exp (-((1 / 2 + ε) * x)) := by
        exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- The zero-side value forced by the totally complex explicit formula. -/
noncomputable def totallyComplexZeroSide
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℂ) (phi : ℂ → ℂ)
    (archimedeanIntegral primeSide : ℂ) : ℂ :=
  (phi 0 + phi 1)
    + ((Real.log |(discr K : ℝ)| : ℝ) : ℂ) * F 0
    - ((finrank ℚ K : ℕ) : ℂ)
        * ((Real.eulerMascheroniConstant + Real.log (8 * Real.pi) : ℝ) : ℂ) * F 0
    + ((finrank ℚ K : ℕ) : ℂ) * archimedeanIntegral
    - (primeSide + primeSide)

theorem totallyComplexExplicitFormula_zeroSide
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (F : ℝ → ℂ) (phi : ℂ → ℂ) (archimedeanIntegral primeSide : ℂ)
    (hF : DedekindResidue.IsAdmissibleTestFn F) :
    TotallyComplexExplicitFormula K F phi
      (totallyComplexZeroSide K F phi archimedeanIntegral primeSide)
      archimedeanIntegral primeSide := by
  refine ⟨hF, ?_⟩
  rfl

/-- The general Weil limit specializes to the totally complex zero-side expression. -/
theorem weilLimit_eq_totallyComplexZeroSide
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (F : ℝ → ℂ) (primeSide : ℂ) :
    ((DedekindResidue.paperPhi F 0 + DedekindResidue.paperPhi F 1)
      + ((Real.log |NumberField.discr K| : ℝ) : ℂ) * F 0
      + (((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
          + 2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
            * (Real.eulerMascheroniConstant + Real.log (8 * Real.pi))
          + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (Real.pi / 2)) : ℝ)) : ℂ) * F 0
      + (((NumberField.InfinitePlace.nrRealPlaces K
          + 2 * NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
          * (∫ x in Set.Ioi (0 : ℝ),
            ((1 / (2 * Real.sinh (x / 2)) : ℝ) : ℂ) * (F 0 - F x))
      + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
          * (∫ x in Set.Ioi (0 : ℝ),
            ((1 / (2 * Real.cosh (x / 2)) : ℝ) : ℂ) * (F 0 - F x))
      - (primeSide + primeSide)) =
        totallyComplexZeroSide K F (DedekindResidue.paperPhi F)
          (poitouArchimedeanIntegral F) primeSide := by
  rw [totallyComplexZeroSide, poitouArchimedeanIntegral,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
    NumberField.IsTotallyComplex.finrank]
  norm_num
  ring

theorem totallyComplexZeroSide_nonneg_of_poitouWindowLimit
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℂ) (f : ℝ → ℝ)
    (archimedeanIntegral primeSide : ℂ) {a : ℝ} {T : ℕ → ℝ}
    (hF : DedekindResidue.IsAdmissibleTestFn F)
    (hboundary : PoitouBoundaryIdentification (DedekindResidue.paperPhi F) f)
    (hfourier : ∀ t, 0 ≤ (𝓕 (complexify f) t).re)
    (hlimit : Tendsto (fun n : ℕ => ∑ᶠ z,
      ((MeromorphicOn.divisor
        (DedekindResidue.completedDedekindZetaEntire K)
        (Set.Ioo (-a) (1 + a) ×ℂ Set.Ioo (-(T n)) (T n))) z : ℂ) *
          DedekindResidue.paperPhi F z)
      atTop (nhds (totallyComplexZeroSide K F (DedekindResidue.paperPhi F)
        archimedeanIntegral primeSide))) :
    0 ≤ (totallyComplexZeroSide K F (DedekindResidue.paperPhi F)
      archimedeanIntegral primeSide).re := by
  have hwindow (n : ℕ) : 0 ≤ (∑ᶠ z,
      ((MeromorphicOn.divisor
        (DedekindResidue.completedDedekindZetaEntire K)
        (Set.Ioo (-a) (1 + a) ×ℂ Set.Ioo (-(T n)) (T n))) z : ℂ) *
          DedekindResidue.paperPhi F z).re :=
    zeroWindow_re_nonneg K (DedekindResidue.paperPhi F) f hboundary hfourier
      (paperPhi_diffContOnCl_of_isAdmissible hF)
      (paperPhi_bddAbove_of_isAdmissible hF)
      (DedekindResidue.isBounded_Ioo_reProdIm (-a) (1 + a) (-(T n)) (T n))
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hlimit
  exact isClosed_Ici.mem_of_tendsto hre (Filter.Eventually.of_forall hwindow)

theorem totallyComplexExplicitFormula_of_poitouWindowLimit
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (F : ℝ → ℂ) (f : ℝ → ℝ)
    (archimedeanIntegral primeSide : ℂ) {a : ℝ} {T : ℕ → ℝ}
    (hF : DedekindResidue.IsAdmissibleTestFn F)
    (hboundary : PoitouBoundaryIdentification (DedekindResidue.paperPhi F) f)
    (hfourier : ∀ t, 0 ≤ (𝓕 (complexify f) t).re)
    (hlimit : Tendsto (fun n : ℕ => ∑ᶠ z,
      ((MeromorphicOn.divisor
        (DedekindResidue.completedDedekindZetaEntire K)
        (Set.Ioo (-a) (1 + a) ×ℂ Set.Ioo (-(T n)) (T n))) z : ℂ) *
          DedekindResidue.paperPhi F z)
      atTop (nhds (totallyComplexZeroSide K F (DedekindResidue.paperPhi F)
        archimedeanIntegral primeSide))) :
    TotallyComplexExplicitFormula K F (DedekindResidue.paperPhi F)
        (totallyComplexZeroSide K F (DedekindResidue.paperPhi F)
          archimedeanIntegral primeSide)
        archimedeanIntegral primeSide
      ∧ 0 ≤ (totallyComplexZeroSide K F (DedekindResidue.paperPhi F)
        archimedeanIntegral primeSide).re :=
  ⟨totallyComplexExplicitFormula_zeroSide K F (DedekindResidue.paperPhi F)
      archimedeanIntegral primeSide hF,
    totallyComplexZeroSide_nonneg_of_poitouWindowLimit K F f
      archimedeanIntegral primeSide hF hboundary hfourier hlimit⟩

/-- A convergent Weil window sequence for a Gaussian Tartar approximant supplies the
explicit-formula package and its nonnegative zero side. -/
theorem gaussianTartarExplicitFormula_of_window_limit
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    {y : ℝ} (hy : 0 < y) (n : ℕ) {a : ℝ} {T : ℕ → ℝ}
    (hlimit : Tendsto (fun m : ℕ => ∑ᶠ z,
      ((MeromorphicOn.divisor
        (DedekindResidue.completedDedekindZetaEntire K)
        (Set.Ioo (-a) (1 + a) ×ℂ Set.Ioo (-(T m)) (T m))) z : ℂ) *
          DedekindResidue.paperPhi
            (gaussianPoitouApproximant
              (scaledNumerator tartarNumerator (1 / √y)) n) z)
      atTop (nhds (totallyComplexZeroSide K
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n)
        (DedekindResidue.paperPhi
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (poitouArchimedeanIntegral
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (DedekindResidue.primeSideH K a
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n) 0)))) :
    TotallyComplexExplicitFormula K
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n)
        (DedekindResidue.paperPhi
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (totallyComplexZeroSide K
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n)
          (DedekindResidue.paperPhi
            (gaussianPoitouApproximant
              (scaledNumerator tartarNumerator (1 / √y)) n))
          (poitouArchimedeanIntegral
            (gaussianPoitouApproximant
              (scaledNumerator tartarNumerator (1 / √y)) n))
          (DedekindResidue.primeSideH K a
            (gaussianPoitouApproximant
              (scaledNumerator tartarNumerator (1 / √y)) n) 0))
        (poitouArchimedeanIntegral
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (DedekindResidue.primeSideH K a
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n) 0)
      ∧ 0 ≤ (totallyComplexZeroSide K
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n)
        (DedekindResidue.paperPhi
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (poitouArchimedeanIntegral
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (DedekindResidue.primeSideH K a
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n) 0)).re := by
  have hscale : 0 < 1 / √y := by positivity
  apply totallyComplexExplicitFormula_of_poitouWindowLimit K
    (gaussianPoitouApproximant
      (scaledNumerator tartarNumerator (1 / √y)) n)
    (gaussianDampedNumerator
      (scaledNumerator tartarNumerator (1 / √y)) n)
  · exact gaussianPoitouApproximant_isAdmissible_scaledTartar hscale.ne' n
  · exact gaussianPoitouApproximant_scaledTartar_boundaryIdentification hscale.ne' n
  · exact fourier_gaussianDamped_scaledTartar_nonneg hscale n
  · exact hlimit

private theorem norm_gaussianTartar_weighted_le
    (b : ℝ) (n : ℕ) (a x : ℝ) :
    ‖gaussianPoitouApproximant (scaledNumerator tartarNumerator b) n x *
        ((Real.exp ((1 / 2 + a) * x) : ℝ) : ℂ)‖
      ≤ Real.exp (((n : ℝ) + 1) * (1 / 2 + a) ^ 2 / 4) := by
  have hnum0 : 0 ≤ scaledNumerator tartarNumerator b x := tartarNumerator_nonneg _
  have hnum1 : scaledNumerator tartarNumerator b x ≤ 1 := tartarNumerator_le_one _
  have hcut0 : 0 ≤ poitouGaussianCutoff n x := (poitouGaussianCutoff_pos n x).le
  have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
  have hquot0 : 0 ≤ gaussianDampedNumerator
      (scaledNumerator tartarNumerator b) n x / Real.cosh (x / 2) := by
    exact div_nonneg (mul_nonneg hnum0 hcut0) (Real.cosh_pos _).le
  simp only [gaussianPoitouApproximant, poitouKernel_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquot0, Real.abs_exp]
  have hbase : gaussianDampedNumerator (scaledNumerator tartarNumerator b) n x /
      Real.cosh (x / 2) ≤ poitouGaussianCutoff n x := by
    unfold gaussianDampedNumerator
    calc
      scaledNumerator tartarNumerator b x * poitouGaussianCutoff n x /
          Real.cosh (x / 2)
          ≤ poitouGaussianCutoff n x / Real.cosh (x / 2) := by
            exact div_le_div_of_nonneg_right
              (mul_le_of_le_one_left hcut0 hnum1) (Real.cosh_pos _).le
      _ ≤ poitouGaussianCutoff n x := by
        exact div_le_self hcut0 hcosh
  calc
    gaussianDampedNumerator (scaledNumerator tartarNumerator b) n x /
          Real.cosh (x / 2) * Real.exp ((1 / 2 + a) * x)
        ≤ poitouGaussianCutoff n x * Real.exp ((1 / 2 + a) * x) := by
          gcongr
    _ = Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (1 / 2 + a) * x) := by
      rw [poitouGaussianCutoff, ← Real.exp_add]
    _ ≤ Real.exp (((n : ℝ) + 1) * (1 / 2 + a) ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      have hc : 0 < (n : ℝ) + 1 := by positivity
      have hquad :
          -x ^ 2 + ((n : ℝ) + 1) * (1 / 2 + a) * x ≤
            ((n : ℝ) + 1) ^ 2 * (1 / 2 + a) ^ 2 / 4 := by
        nlinarith [sq_nonneg (2 * x - ((n : ℝ) + 1) * (1 / 2 + a))]
      calc
        -x ^ 2 / ((n : ℝ) + 1) + (1 / 2 + a) * x =
            (-x ^ 2 + ((n : ℝ) + 1) * (1 / 2 + a) * x) /
              ((n : ℝ) + 1) := by field_simp
        _ ≤ (((n : ℝ) + 1) ^ 2 * (1 / 2 + a) ^ 2 / 4) /
              ((n : ℝ) + 1) := (div_le_div_iff_of_pos_right hc).2 hquad
        _ = ((n : ℝ) + 1) * (1 / 2 + a) ^ 2 / 4 := by field_simp

/-- The prime side of every Gaussian Tartar approximant is nonnegative. -/
theorem primeSideH_gaussianTartar_nonneg
    (K : Type*) [Field K] [NumberField K]
    (b : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 ≤ (DedekindResidue.primeSideH K a
      (gaussianPoitouApproximant (scaledNumerator tartarNumerator b) n) 0).re := by
  rw [DedekindResidue.primeSideH]
  let C := Real.exp (((n : ℝ) + 1) * (1 / 2 + a) ^ 2 / 4)
  have hsum : Summable (fun pk :
      {p : Ideal (𝓞 K) // p.IsPrime ∧ p ≠ ⊥} × ℕ =>
      ((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^
            (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + a)) : ℝ) : ℂ) *
        (gaussianPoitouApproximant (scaledNumerator tartarNumerator b) n
            (0 + (((pk.2 + 1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1)) *
          ((Real.exp ((1 / 2 + a) *
            (0 + (((pk.2 + 1 : ℕ)) : ℝ) *
              Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))) := by
    refine Summable.of_norm_bounded
      ((DedekindResidue.summable_primeIdeal_pow_log_rpow K
        (by linarith : (1 : ℝ) < 1 + a)).mul_right C) ?_
    intro pk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (DedekindResidue.primeSideH_weight_nonneg K pk)]
    exact mul_le_mul_of_nonneg_left
      (norm_gaussianTartar_weighted_le b n a _)
      (DedekindResidue.primeSideH_weight_nonneg K pk)
  rw [Complex.re_tsum hsum]
  apply tsum_nonneg
  intro pk
  have hF : 0 ≤ (gaussianPoitouApproximant
      (scaledNumerator tartarNumerator b) n
      ((((pk.2 + 1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))).re := by
    simp only [gaussianPoitouApproximant, poitouKernel_apply, Complex.ofReal_re]
    exact div_nonneg
      (mul_nonneg (tartarNumerator_nonneg _) (poitouGaussianCutoff_pos _ _).le)
      (Real.cosh_pos _).le
  simp only [zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [zero_mul, sub_zero]
  exact mul_nonneg (DedekindResidue.primeSideH_weight_nonneg K pk)
    (mul_nonneg hF (Real.exp_pos _).le)

end Odlyzko
