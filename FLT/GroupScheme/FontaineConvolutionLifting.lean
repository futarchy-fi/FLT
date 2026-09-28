/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineConvolutionApproximation
public import FLT.GroupScheme.FontaineCubicLifting
public import FLT.Mathlib.Analysis.Normed.Algebra.Convolution
public import FLT.Mathlib.Analysis.Normed.Algebra.CubicRoot

/-!
# Compatible lifting of arbitrary killed-by-three models

Lift a truncated algebra point to a linear functional, correct its convolution
cube in the complete finite-dimensional convolution algebra, and recover all
algebra laws by separation. The cubic contraction retains the factor of three
in the quadratic term, giving the threshold `m > 3/2` and precision loss one.
No polynomial presentation or complete-intersection hypothesis is needed.
-/

@[expose] public noncomputable section

open WithConv

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]
  {A : Type*} [CommRing A] [Bialgebra ℤ_[3] A] [Coalgebra.IsCocomm ℤ_[3] A]
  [Module.Free ℤ_[3] A] [Module.Finite ℤ_[3] A]

/-- Every integral approximate convolution cube root lifts to an exact one
with precision loss one when the original precision exceeds three halves. -/
theorem exists_integral_conv_cube_correction
    (F : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E))
    {m : ℚ} (hm : 3 / 2 < m)
    (herr : ∀ a, (F ^ 3 - 1).ofConv a ∈ threeAdicValuationIdeal E m) :
    ∃ G : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E), G ^ 3 = 1 ∧
      ∀ a, (G - F).ofConv a ∈ threeAdicValuationIdeal E (m - 1) := by
  classical
  let normedField := spectralNorm.nontriviallyNormedField ℚ_[3] E
  let charZeroE : CharZero E := Algebra.charZero_of_charZero ℚ_[3] E
  let b := Module.Free.chooseBasis ℤ_[3] A
  have hna := isNonarchimedean_spectralNorm (K := ℚ_[3]) (L := E)
  have hbase (r : ℤ_[3]) : ‖algebraMap ℤ_[3] E r‖ ≤ 1 :=
    (isIntegral_iff_spectralNorm_le_one E _).mp (isIntegral_algebraMap)
  let convolutionRing := b.convolutionNormedCommRing hna hbase
  let convolutionAlgebra := b.convolutionNormedAlgebra hna hbase
  let convolutionComplete := b.convolution_completeSpace (E := E)
  let q := (ThreeAdicIntegers E).val
  let X : WithConv (A →ₗ[ℤ_[3]] E) := toConv (q.toLinearMap.comp F.ofConv)
  let ρ := (3 : ℝ) ^ (-((m - 1 : ℚ) : ℝ))
  have hρ : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  obtain ⟨hρ1, hρ2⟩ := cubic_hensel_radius_bounds hm
  have hX : ‖X‖ ≤ 1 := by
    rw [b.convolution_norm_eq]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    exact (isIntegral_iff_spectralNorm_le_one E _).mp (F (b i)).property
  have herror : ‖X ^ 3 - 1‖ ≤ (3 : ℝ) ^ (-(m : ℝ)) := by
    rw [b.convolution_norm_eq]
    apply (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg (by norm_num) _)).mpr
    intro i
    have hp := LinearMap.congr_fun (LinearMap.convPow_postcomp_algHom q F 3) (b i)
    have he : (X ^ 3 - 1).ofConv (b i) = q ((F ^ 3 - 1).ofConv (b i)) := by
      change (X ^ 3).ofConv (b i) - (1 : WithConv (A →ₗ[ℤ_[3]] E)).ofConv (b i) =
        q ((F ^ 3).ofConv (b i) - (1 : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E)).ofConv (b i))
      simp only [map_sub, LinearMap.convOne_apply, AlgHom.commutes]
      exact congrArg (fun z ↦ z - algebraMap ℤ_[3] E (Coalgebra.counit (b i))) hp.symm
    rw [he]
    exact herr (b i)
  have hq : ‖X ^ 3 - 1‖ < 1 := herror.trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by exact_mod_cast (show -m < 0 by linarith)))
  have hthree : ‖(3 : E)⁻¹‖ = 3 := by
    have hh : ‖(3 : E)‖ = (3 : ℝ)⁻¹ := spectralNorm_three E
    rw [norm_inv, hh]
    norm_num
  have hinit : ‖(3 : E)⁻¹‖ * ‖X ^ 3 - 1‖ ≤ ρ := by
    rw [hthree]
    calc
      _ ≤ 3 * (3 : ℝ) ^ (-(m : ℝ)) := mul_le_mul_of_nonneg_left herror (by norm_num)
      _ = ρ := by
        dsimp only [ρ]
        nth_rw 1 [← Real.rpow_one 3]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        push_cast
        ring
  have hcubic : ‖(3 : E)⁻¹‖ * ρ ^ 2 < 1 := by
    rw [hthree]
    calc
      _ < 3 * (3 : ℝ)⁻¹ := mul_lt_mul_of_pos_left hρ2 (by norm_num)
      _ = 1 := by norm_num
  obtain ⟨Y, hYclose, hYcube⟩ :=
    (b.convolution_isNonarchimedean hna).exists_cube_root_near_one_algebra
      X (3 : E)⁻¹ (by norm_num) hρ hρ1 hX hq hinit hcubic
  have hclose (a : A) : ‖Y a - X a‖ ≤ ρ :=
    (b.norm_apply_le_convolution_norm hna hbase (Y - X) a).trans hYclose
  have hYint (a : A) : IsIntegral ℤ_[3] (Y a) := by
    apply (isIntegral_iff_spectralNorm_le_one E _).mpr
    have hh := hna (Y a - X a) (X a)
    rw [sub_add_cancel] at hh
    exact hh.trans (max_le ((hclose a).trans hρ1.le)
      ((b.norm_apply_le_convolution_norm hna hbase X a).trans hX))
  let G : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E) :=
    toConv (Y.ofConv.codRestrict (ThreeAdicIntegers E).toSubmodule hYint)
  have hGcoe : q.toLinearMap.comp G.ofConv = Y.ofConv := rfl
  refine ⟨G, ?_, fun a ↦ hclose a⟩
  apply WithConv.ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  have hp := LinearMap.convPow_postcomp_algHom q G 3
  rw [hGcoe, toConv_ofConv, hYcube] at hp
  have hh := LinearMap.congr_fun hp a
  change q ((G ^ 3).ofConv a) = q ((1 : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E)).ofConv a)
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.convOne_apply, AlgHom.commutes] using hh

/-- Every truncated point of an arbitrary killed-by-three finite flat model
lifts integrally, agreeing modulo valuation at least `m - 1` for `m > 3/2`. -/
theorem FF.exists_compatible_integral_point (M : FF ℤ_[3] ℚ_[3])
    (hM : KilledBy 3 M) {m : ℚ} (hm : 3 / 2 < m)
    (u : M.CoordinateRing →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) :
    ∃ v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E,
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
        (Ideal.Quotient.factorₐ ℤ_[3]
          (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp u := by
  let freeCoordinateRing : Module.Free ℤ_[3] M.CoordinateRing :=
    Module.free_of_flat_of_isLocalRing
  let cocommCoordinateRing := M.coordinateRing_cocomm
  obtain ⟨F, hF, herr⟩ := M.exists_approximate_conv_cube_root E hM m u
  obtain ⟨G, hG, hclose⟩ := exists_integral_conv_cube_correction E F hm herr
  exact M.exists_compatible_point_of_conv_correction E hm u F G hF hG hclose

end ThreeAdicPlan
