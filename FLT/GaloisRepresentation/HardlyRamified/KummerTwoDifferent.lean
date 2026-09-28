/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoClassNumber
public import FLT.NumberField.DifferentExponentBounds

/-!
# The dyadic different of the sextic Kummer field

The explicit integral family has discriminant `-34992 = -2^4 * 3^7`.
Its divisibility by the field discriminant bounds the dyadic different exponent
by two, since the dyadic residue degree is two. The ramification index three
provides the matching lower bound.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open NumberField Polynomial UniqueFactorizationMonoid

/-- The explicit integral family gives divisibility, not just a size bound. -/
theorem discr_kummerTwoField_dvd : discr K₀ ∣ (34992 : ℤ) := by
  obtain ⟨a, ha⟩ := exists_integral_cubeRoot_two
  obtain ⟨z, hz⟩ := exists_integral_thirdRoot
  obtain ⟨r, hr⟩ := exists_integral_discriminantElement a z ha hz
  let v : Fin 6 → 𝓞 K₀ := ![1, a, a ^ 2, z, a * z, r]
  have ha' : (a : K₀) ^ 3 = 2 := by
    have h := congrArg (algebraMap (𝓞 K₀) K₀) ha
    simpa only [map_pow, map_ofNat] using h
  have hz' : (z : K₀) ^ 2 + (z : K₀) + 1 = 0 := by
    have h := congrArg (algebraMap (𝓞 K₀) K₀) hz
    simpa only [map_pow, map_add, map_one, map_zero] using h
  have hr' : (r : K₀) = ((a : K₀) + 1) ^ 2 * ((z : K₀) + 2) / 3 := by
    have h := congrArg (algebraMap (𝓞 K₀) K₀) hr
    simp only [map_mul, map_ofNat, map_pow, map_add, map_one] at h
    apply (eq_div_iff (by norm_num : (3 : K₀) ≠ 0)).mpr
    simpa only [mul_comm] using h
  have hv : (fun i ↦ (v i : K₀)) =
      (![1, (a : K₀), (a : K₀) ^ 2, (z : K₀), (a : K₀) * (z : K₀),
        ((a : K₀) + 1) ^ 2 * ((z : K₀) + 2) / 3] : Fin 6 → K₀) := by
    ext i
    fin_cases i <;> simp [v, hr']
  have hd : Algebra.discr ℤ v = -34992 := by
    apply Int.cast_injective (α := ℚ)
    rw [coe_discr_integral_family, hv, discr_sextic_family _ _ ha' hz']
    norm_num
  have hdvd : discr K₀ ∣ (34992 : ℤ) := by
    have h := discr_dvd_integral_family v
    rw [hd] at h
    exact dvd_neg.mp h
  exact hdvd

/-- The different of the sextic Kummer field has exponent two at every dyadic prime. -/
theorem differentExponentAt_kummerTwoField_two
    (P : Ideal (𝓞 K₀)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})] :
    differentExponentAt K₀ P = 2 := by
  classical
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(2 : ℤ)}) (by simp) P
  have : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨a, ha⟩ := exists_integral_cubeRoot_two
  have hcube : P ^ 3 = Ideal.map (algebraMap ℤ (𝓞 K₀)) (Ideal.span {(2 : ℤ)}) := by
    rw [primeAboveTwo_eq_span_cubeRoot P a ha, Ideal.span_singleton_pow, ha]
    simp only [Ideal.map_span, Set.image_singleton, map_ofNat]
  have hlo : P ^ 2 ∣ differentIdeal ℤ (𝓞 K₀) := by
    exact pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(2 : ℤ)}) P 3
      (by simp) (by rw [hcube])
  have hnorm : Ideal.absNorm P = 4 := by
    have hh := Ideal.natAbs_pow_inertiaDeg (2 : ℤ) P
    rw [(ramification_inertia_at_two P).2] at hh
    norm_num at hh
    exact hh.symm
  have hhi : ¬ P ^ 3 ∣ differentIdeal ℤ (𝓞 K₀) := by
    intro h
    have hn := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp h)
    rw [map_pow, hnorm, absNorm_differentIdeal K₀ (𝓞 K₀)] at hn
    have hd : (discr K₀).natAbs ∣ 34992 := by
      simpa using Int.natAbs_dvd_natAbs.mpr discr_kummerTwoField_dvd
    norm_num at hn
    have hh := hn.trans hd
    norm_num at hh
  exact count_normalizedFactors_eq
    (Ideal.prime_of_isPrime hP inferInstance).irreducible (normalize_eq P) hlo hhi

/-- The tame different formula at two for the sextic Kummer field. -/
theorem differentExponentAt_kummerTwoField_eq_ramificationIdx_sub_one
    (P : Ideal (𝓞 K₀)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})] :
    differentExponentAt K₀ P = P.ramificationIdx ℤ - 1 := by
  rw [differentExponentAt_kummerTwoField_two P, ramificationIdx_at_two P]

end ThreeAdicPlan
