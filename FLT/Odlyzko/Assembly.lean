/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.DegreeEighteen
public import FLT.Odlyzko.ExponentialForm
public import FLT.Odlyzko.PoitouAdmissibility
public import FLT.Odlyzko.PoitouArchimedean
public import FLT.Odlyzko.PoitouBoundary
public import FLT.Odlyzko.WeilDecay

/-!
# Assembly of the Odlyzko discriminant bound

This file passes the Gaussian Tartar explicit formulas to their Poitou limit, applies the
certified degree-eighteen estimate, and converts the logarithmic bound to the required
natural-power inequality.
-/

@[expose] public section

open Filter Module NumberField

namespace Odlyzko

/-- The regularized Weil--Poitou formula at a scale in the certified large-parameter range. -/
theorem log_discriminant_ge_scaledTartar
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    {y : ℝ} (hy : 0 < y) (hy9 : y < 9 / 4) :
    (finrank ℚ K : ℝ) *
          (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - Poitou.L1large y) -
        12 * Real.pi / (5 * Real.sqrt y) ≤ Real.log |(discr K : ℝ)| := by
  let f := scaledNumerator tartarNumerator (1 / Real.sqrt y)
  let phi : ℕ → ℂ → ℂ := fun n =>
    DedekindResidue.paperPhi (gaussianPoitouApproximant f n)
  let archimedeanIntegral : ℕ → ℂ := fun n =>
    poitouArchimedeanIntegral (gaussianPoitouApproximant f n)
  let primeSide : ℕ → ℂ := fun n =>
    DedekindResidue.primeSideH K (1 / 8) (gaussianPoitouApproximant f n) 0
  let zeroSide : ℕ → ℂ := fun n =>
    totallyComplexZeroSide K (gaussianPoitouApproximant f n) (phi n)
      (archimedeanIntegral n) (primeSide n)
  have harch :=
    Poitou.tendsto_archimedeanLowerTerm_gaussian_scaledTartar_large hy hy9
  have hpole := tendsto_gaussianPoitouApproximant_scaledTartar_poleCorrection hy
  have hlimit : Tendsto
      (fun n => (finrank ℚ K : ℝ) * archimedeanLowerTerm (archimedeanIntegral n) -
        (phi n 0 + phi n 1).re)
      atTop
      (nhds ((finrank ℚ K : ℝ) *
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - Poitou.L1large y) -
          12 * Real.pi / (5 * Real.sqrt y))) := by
    simpa [f, phi, archimedeanIntegral] using
      (harch.const_mul (finrank ℚ K : ℝ)).sub hpole
  apply log_discriminant_ge_of_poitouRegularization K f
    (scaledTartarPoitouRegularization hy) phi zeroSide archimedeanIntegral primeSide
    (limit := (finrank ℚ K : ℝ) *
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - Poitou.L1large y) -
        12 * Real.pi / (5 * Real.sqrt y))
  · intro n
    simpa [f, phi, zeroSide, archimedeanIntegral, primeSide,
      scaledTartarPoitouRegularization] using (gaussianTartarExplicitFormula K hy n).1
  · intro n
    simp [f, scaledTartarPoitouRegularization, gaussianPoitouApproximant,
      scaledNumerator]
  · intro n
    simpa [f, phi, zeroSide, archimedeanIntegral, primeSide] using
      (gaussianTartarExplicitFormula K hy n).2
  · intro n
    simpa [f, primeSide] using
      (primeSideH_gaussianTartar_nonneg K (1 / Real.sqrt y) n
        (a := (1 / 8 : ℝ)) (by norm_num))
  · exact hlimit

/-- The assembled logarithmic root-discriminant bound in every degree at least eighteen. -/
theorem log_eightPointTwoFive_le_log_discriminant_div_finrank
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) :
    Real.log 8.25 ≤ Real.log |(discr K : ℝ)| / finrank ℚ K := by
  have hn : 0 < finrank ℚ K := lt_of_lt_of_le (by norm_num) hdim
  have hnR : (0 : ℝ) < finrank ℚ K := by exact_mod_cast hn
  have h18R : (18 : ℝ) ≤ finrank ℚ K := by exact_mod_cast hdim
  have hpole : 0 < 12 * Real.pi / (5 * Real.sqrt Poitou.y0) := by
    rw [Poitou.sqrt_y0]
    positivity
  have hraw := log_discriminant_ge_scaledTartar K
    (y := Poitou.y0) (by norm_num [Poitou.y0]) (by norm_num [Poitou.y0])
  have hroot :
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - Poitou.L1large Poitou.y0 -
          12 * Real.pi / (5 * Real.sqrt Poitou.y0) / finrank ℚ K ≤
        Real.log |(discr K : ℝ)| / finrank ℚ K := by
    apply (le_div_iff₀ hnR).2
    calc
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
            Poitou.L1large Poitou.y0 -
          12 * Real.pi / (5 * Real.sqrt Poitou.y0) / finrank ℚ K) *
            finrank ℚ K =
          (finrank ℚ K : ℝ) *
              (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
                Poitou.L1large Poitou.y0) -
            12 * Real.pi / (5 * Real.sqrt Poitou.y0) := by
              field_simp [hnR.ne']
      _ ≤ Real.log |(discr K : ℝ)| := hraw
  have hpole_mono :
      12 * Real.pi / (5 * Real.sqrt Poitou.y0) / finrank ℚ K ≤
        12 * Real.pi / (5 * Real.sqrt Poitou.y0) / 18 :=
    div_le_div_of_nonneg_left hpole.le (by norm_num) h18R
  apply Poitou.degree_eighteen_bound.trans
  rw [Poitou.degreeEighteenLowerBound]
  have h := (sub_le_sub_left hpole_mono
    (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
      Poitou.L1large Poitou.y0)).trans hroot
  convert h using 1
  ring

/-- The complete Odlyzko bound, assembled from the Weil formula and the certified endpoint. -/
theorem discriminant_ge_eightPointTwoFive_pow
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) :
    |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K :=
  discriminant_ge_pow_of_log_bound K
    (log_eightPointTwoFive_le_log_discriminant_div_finrank K hdim)

end Odlyzko
