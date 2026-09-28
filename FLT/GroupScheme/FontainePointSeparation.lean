/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineQuotientValuation
public import FLT.GroupScheme.FiniteFlatDifferentials

/-!
# Separation of three-torsion integral points

The cubic convolution identity shows that a point of order dividing three
cannot be nontrivial and closer to the identity than valuation one half.
This proves uniqueness, not existence, in Fontaine's lifting argument.
-/

@[expose] public noncomputable section

open WithConv

namespace LinearMap

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Bialgebra R A] [Algebra R B]

/-- Convolution multiplies ideals containing the values of its factors. -/
theorem convMul_mem_ideal_mul (F G : WithConv (A →ₗ[R] B)) (I J : Ideal B)
    (hF : ∀ x, F.ofConv x ∈ I) (hG : ∀ x, G.ofConv x ∈ J) (x : A) :
    (F * G).ofConv x ∈ I * J := by
  rw [(Coalgebra.Repr.arbitrary R x).convMul_apply]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_mul (hF _) (hG _)

end LinearMap

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- An integral element of valuation greater than one half has norm less
than one and square of norm less than the norm of three. -/
theorem norm_bounds_of_mem_valuationIdeal {t : ℚ} (ht : 1 / 2 < t)
    (c : ThreeAdicIntegers E) (hc : c ∈ threeAdicValuationIdeal E t) :
    spectralNorm ℚ_[3] E (c : E) < 1 ∧
      (spectralNorm ℚ_[3] E (c : E)) ^ 2 < (3 : ℝ)⁻¹ := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show (0 : ℚ) < t by linarith)
  have hc' := hc
  change spectralNorm ℚ_[3] E (c : E) ≤ (3 : ℝ) ^ (-(t : ℝ)) at hc'
  constructor
  · exact hc'.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht0))
  · have hpow := pow_le_pow_left₀ (spectralNorm_nonneg (c : E)) hc' 2
    apply hpow.trans_lt
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_neg_one]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have ht' : (1 / 2 : ℝ) < (t : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr ht
    norm_num only [Nat.cast_ofNat]
    linarith

variable {A : Type*} [CommRing A] [Bialgebra ℤ_[3] A] [Coalgebra.IsCocomm ℤ_[3] A]

/-- A convolution element killed by cubing and congruent to one at precision
greater than one half is one. The target is the full ring of integers. -/
theorem conv_eq_one_of_cube_eq_one_of_close {t : ℚ} (ht : 1 / 2 < t)
    (F : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E)) (hF : F ^ 3 = 1)
    (hclose : ∀ x, (F - 1).ofConv x ∈ threeAdicValuationIdeal E t) : F = 1 := by
  let D := F - 1
  let I : Ideal (ThreeAdicIntegers E) := Ideal.span (Set.range D.ofConv)
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  change I = Ideal.span {c} at hc
  have hD (x : A) : D.ofConv x ∈ Ideal.span {c} := by
    rw [← hc]
    exact Ideal.subset_span ⟨x, rfl⟩
  have hcI : c ∈ I := by rw [hc]; exact Ideal.subset_span (Set.mem_singleton _)
  have hcclose : c ∈ threeAdicValuationIdeal E t := by
    apply (Ideal.span_le.mpr ?_ : I ≤ threeAdicValuationIdeal E t) hcI
    rintro _ ⟨x, rfl⟩
    exact hclose x
  by_cases hc0 : c = 0
  · apply sub_eq_zero.mp
    apply WithConv.ext
    apply LinearMap.ext
    intro x
    have hx := hD x
    change D.ofConv x = 0
    simpa only [hc0, Ideal.span_singleton_zero, Ideal.mem_bot] using hx
  have hD2 (x : A) : (D ^ 2).ofConv x ∈ Ideal.span {c ^ 2} := by
    rw [← Ideal.span_singleton_pow, pow_two]
    simpa only [pow_two] using LinearMap.convMul_mem_ideal_mul D D _ _ hD hD x
  have hD3 (x : A) : (D ^ 3).ofConv x ∈ Ideal.span {c ^ 3} := by
    rw [← Ideal.span_singleton_pow, pow_succ, pow_succ D 2]
    exact LinearMap.convMul_mem_ideal_mul (D ^ 2) D _ _
      (fun x ↦ by simpa only [Ideal.span_singleton_pow] using hD2 x) hD x
  have hid : (3 : ℕ) • D = -((3 : ℕ) • D ^ 2 + D ^ 3) := by
    have hh : (D + 1) ^ 3 = 1 := by simpa only [D, sub_add_cancel] using hF
    simp only [nsmul_eq_mul]
    linear_combination hh
  let J : Ideal (ThreeAdicIntegers E) := Ideal.span {3 * c ^ 2, c ^ 3}
  have hthree (x : A) : (3 : ThreeAdicIntegers E) * D.ofConv x ∈ J := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hD2 x)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hD3 x)
    have hx := congrArg (fun T : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E) ↦ T.ofConv x) hid
    change (3 : ℕ) • D.ofConv x = -((3 : ℕ) • (D ^ 2).ofConv x + (D ^ 3).ofConv x) at hx
    simp only [nsmul_eq_mul, Nat.cast_ofNat, ha, hb] at hx
    rw [hx]
    apply J.neg_mem
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by ring⟩
  have hIJ : (I : Submodule (ThreeAdicIntegers E) (ThreeAdicIntegers E)) ≤
      Submodule.comap (LinearMap.mul (ThreeAdicIntegers E) (ThreeAdicIntegers E) 3)
        (J : Submodule (ThreeAdicIntegers E) (ThreeAdicIntegers E)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hthree x
  have hcJ : (3 : ThreeAdicIntegers E) * c ∈ J := hIJ hcI
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hcJ
  have hab' : a * 3 * c + b * c ^ 2 = (3 : ThreeAdicIntegers E) := by
    apply mul_right_cancel₀ hc0
    linear_combination hab
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  obtain ⟨hc1, hc2⟩ := norm_bounds_of_mem_valuationIdeal E ht c hcclose
  change ‖(c : E)‖ < 1 at hc1
  change ‖(c : E)‖ ^ 2 < (3 : ℝ)⁻¹ at hc2
  have ha1 : ‖(a : E)‖ ≤ 1 := (isIntegral_iff_spectralNorm_le_one E _).mp a.property
  have hb1 : ‖(b : E)‖ ≤ 1 := (isIntegral_iff_spectralNorm_le_one E _).mp b.property
  have habE : (a : E) * 3 * (c : E) + (b : E) * (c : E) ^ 2 = 3 := by
    have h := congrArg (fun z : ThreeAdicIntegers E ↦ (z : E)) hab'
    have h3 : ((3 : ThreeAdicIntegers E) : E) = 3 := map_ofNat (ThreeAdicIntegers E).val 3
    simpa only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow,
      h3] using h
  have hna := isNonarchimedean_spectralNorm (K := ℚ_[3]) (L := E)
    ((a : E) * 3 * (c : E)) ((b : E) * (c : E) ^ 2)
  change ‖(a : E) * 3 * (c : E) + (b : E) * (c : E) ^ 2‖ ≤
    max ‖(a : E) * 3 * (c : E)‖ ‖(b : E) * (c : E) ^ 2‖ at hna
  rw [habE, norm_mul, norm_mul, norm_mul, norm_pow] at hna
  have h31 : ‖(3 : E)‖ = (3 : ℝ)⁻¹ := spectralNorm_three E
  rw [h31] at hna
  have hleft : ‖(a : E)‖ * (3 : ℝ)⁻¹ * ‖(c : E)‖ < (3 : ℝ)⁻¹ := by
    calc
      _ ≤ 1 * (3 : ℝ)⁻¹ * ‖(c : E)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha1 (by positivity)) (norm_nonneg _)
      _ < (3 : ℝ)⁻¹ := by nlinarith
  have hright : ‖(b : E)‖ * ‖(c : E)‖ ^ 2 < (3 : ℝ)⁻¹ :=
    (mul_le_mul_of_nonneg_right hb1 (sq_nonneg _)).trans_lt (by simpa only [one_mul] using hc2)
  exact False.elim ((not_lt_of_ge hna) (max_lt hleft hright))

/-- Two convolution elements of order dividing three agree if their values
agree modulo a valuation ideal of cutoff greater than one half. -/
theorem conv_eq_of_cube_eq_one_of_close {t : ℚ} (ht : 1 / 2 < t)
    (F G : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E))
    (hF : F ^ 3 = 1) (hG : G ^ 3 = 1)
    (hclose : ∀ x, (F - G).ofConv x ∈ threeAdicValuationIdeal E t) : F = G := by
  have hpow : (F * G ^ 2) ^ 3 = 1 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm 2 3, pow_mul, hF, hG, one_pow, mul_one]
  have hdiff : F * G ^ 2 - 1 = (F - G) * G ^ 2 := by
    linear_combination hG
  have hidentity : F * G ^ 2 = 1 := conv_eq_one_of_cube_eq_one_of_close E ht _ hpow (by
    intro x
    rw [hdiff]
    simpa only [Ideal.mul_top] using LinearMap.convMul_mem_ideal_mul
      (F - G) (G ^ 2) (threeAdicValuationIdeal E t) ⊤ hclose (fun _ ↦ trivial) x)
  calc
    F = F * G ^ 3 := by rw [hG, mul_one]
    _ = (F * G ^ 2) * G := by ring
    _ = G := by rw [hidentity, one_mul]

/-- Reduction of integral points of a killed-by-three model is injective at
any precision greater than one half. No lifting-existence hypothesis is used. -/
theorem FF.integralPoint_reduction_injective (M : FF ℤ_[3] ℚ_[3])
    (hM : KilledBy 3 M) {t : ℚ} (ht : 1 / 2 < t) :
    Function.Injective (fun f : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E ↦
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E t)).comp f) := by
  let := M.coordinateRing_cocomm
  intro f g hfg
  have hf : toConv f.toLinearMap ^ 3 = 1 := by
    rw [← AlgHom.toLinearMap_convPow,
      HopfAlgebra.convPow_eq_one_of_id 3 (M.id_convPow_eq_one 3 hM), AlgHom.toLinearMap_convOne]
  have hg : toConv g.toLinearMap ^ 3 = 1 := by
    rw [← AlgHom.toLinearMap_convPow,
      HopfAlgebra.convPow_eq_one_of_id 3 (M.id_convPow_eq_one 3 hM), AlgHom.toLinearMap_convOne]
  have h := conv_eq_of_cube_eq_one_of_close E ht _ _ hf hg (by
    intro x
    apply Ideal.Quotient.eq.mp
    exact DFunLike.congr_fun hfg x)
  exact AlgHom.toLinearMap_injective (toConv_injective h)

end ThreeAdicPlan
