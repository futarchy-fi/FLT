/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicInertia

/-!
# Normalization of the cyclotomic uniformizer

The shifted cyclotomic polynomial is a pure leading power plus p times a
polynomial with constant coefficient one. This identifies the unit needed
to compare a cyclotomic uniformizer with a Kummer uniformizer root.
-/

@[expose] public noncomputable section

attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal mulSemiringActionIntegralClosure
  Subalgebra.algebra CommRing.toCommSemiring

open Polynomial IsLocalRing

namespace LocalCyclotomic

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Eisenstein polynomial has a normalized constant-term factor. -/
theorem shifted_eq_X_pow_add : ∃ g : ℤ_[p][X],
    shifted p = X ^ (p - 1) + C (p : ℤ_[p]) * g ∧ g.coeff 0 = 1 := by
  have hd : C (p : ℤ_[p]) ∣ shifted p - X ^ (p - 1) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i < p - 1
    · have h := (shifted_isEisensteinAt p).mem (by rwa [shifted_natDegree])
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
      simpa [coeff_sub, coeff_X_pow, (Nat.ne_of_lt hi)] using h
    · have hcoeff : (shifted p - X ^ (p - 1)).coeff i = 0 := by
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hi) with rfl | hlt
        · simp [coeff_sub, ← shifted_natDegree p, (shifted_monic p).coeff_natDegree]
        · rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rwa [shifted_natDegree]),
            coeff_X_pow, ite_eq_right (Nat.ne_of_gt hlt), sub_self]
      rw [hcoeff]
      exact dvd_zero _
  obtain ⟨g, hg⟩ := hd
  refine ⟨g, (sub_eq_iff_eq_add.mp hg).trans (add_comm _ _), ?_⟩
  have hc := congrArg (fun f : ℤ_[p][X] ↦ f.coeff 0) hg
  have hn : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.out.one_lt).ne'
  simp only [coeff_sub, shifted_coeff_zero, coeff_X_pow, ite_eq_right hn.symm,
    sub_zero, coeff_C_mul] at hc
  exact mul_left_cancel₀ PadicInt.irreducible_p.ne_zero (by simpa using hc.symm)

local notation "v" => rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "A" => IntegralClosure O Ω

/-- The primitive root, regarded as an integral element. -/
def completionZetaIntegral : A :=
  ⟨completionZeta p, IsIntegral.of_pow hp.out.pos
    (by rw [(completionZeta_spec p).pow_eq_one]; exact isIntegral_one)⟩

/-- The cyclotomic root reduces to one in residue characteristic p. -/
lemma residue_completionZetaIntegral : residue A (completionZetaIntegral p) = 1 := by
  let f : ZMod p →+* ResidueField A :=
    (residueFieldMap v).comp (residueEquiv p).symm.toRingHom
  have : CharP (ResidueField A) p := charP_of_injective_ringHom f.injective p
  apply frobenius_inj (ResidueField A) p
  change residue A (completionZetaIntegral p) ^ p = 1 ^ p
  rw [← map_pow]
  have hz : completionZetaIntegral p ^ p = 1 := Subtype.ext (completionZeta_spec p).pow_eq_one
  rw [hz, map_one, one_pow]

/-- The power of the cyclotomic uniformizer is p times an integral unit. -/
theorem completionZeta_sub_one_pow : ∃ u : Aˣ,
    (completionZetaIntegral p - 1) ^ (p - 1) = (p : A) * u := by
  let eR : ℤ_[p] ≃+* O := (PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ)
    ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  obtain ⟨g, hg, hg0⟩ := shifted_eq_X_pow_add p
  let y : A := completionZetaIntegral p - 1
  let q := g.map eR.toRingHom
  have hy : residue A y = 0 := by simp [y, residue_completionZetaIntegral]
  have hq : residue A (aeval y q) = 1 := by
    simp [aeval_def, Polynomial.hom_eval₂, hy, q, hg0]
  have hu : IsUnit (-aeval y q) := (residue_ne_zero_iff_isUnit _).mp (by
    rw [map_neg, hq]; exact neg_ne_zero.mpr one_ne_zero)
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  have hroot : aeval y ((shifted p).map eR.toRingHom) = 0 := by
    apply Subtype.val_injective
    change (aeval y ((shifted p).map eR.toRingHom) : A).1 = (0 : Ω)
    rw [show (aeval y ((shifted p).map eR.toRingHom) : A).1 =
      aeval y.1 ((shifted p).map eR.toRingHom) from
      (aeval_algHom_apply (IsScalarTower.toAlgHom O A Ω) _ _).symm]
    change aeval (completionZeta p - 1) ((shifted p).map eR.toRingHom) = 0
    have hz := (isRoot_cyclotomic_iff_charZero hp.out.pos).mpr (completionZeta_spec p)
    simpa [shifted, Polynomial.map_comp, map_cyclotomic, aeval_def, eval₂_eq_eval_map,
      eval_comp] using hz
  rw [hg] at hroot
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_mul,
    Polynomial.map_natCast, map_add, map_pow, aeval_X, map_mul, _root_.map_natCast] at hroot
  simpa only [mul_neg] using (eq_neg_of_add_eq_zero_left hroot)

/-- The cyclotomic uniformizer differs from the chosen tame root by an integral unit. -/
theorem exists_unit_cyclotomic_root_ratio : ∃ z : Aˣ,
    (z : A).1 = (completionZeta p - 1) / tameUniformizerRoot v := by
  let eR : ℤ_[p] ≃+* O := (PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ)
    ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  have hpO : Irreducible (p : O) := by
    have h := (MulEquiv.irreducible_iff (f := eR.toMulEquiv)).mpr PadicInt.irreducible_p
    change Irreducible (eR (p : ℤ_[p])) at h
    simpa only [map_natCast] using h
  have hassoc : Associated (tameUniformizer v) (p : O) :=
    Ideal.span_singleton_eq_span_singleton.mp <|
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
        ℚ v (tameUniformizer_spec v)).symm.trans hpO.maximalIdeal_eq
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨w, hw⟩ := completionZeta_sub_one_pow p
  let w' : Aˣ := (Units.map (algebraMap O A).toMonoidHom u) * w
  have hpow : ((completionZeta p - 1) / tameUniformizerRoot v) ^ (p - 1) = (w' : A).1 := by
    rw [div_pow]
    have ha := tameUniformizerRoot_spec v
    rw [residue_natCard] at ha
    rw [ha]
    have hw' := congrArg (fun x : A ↦ x.1) hw
    change (completionZeta p - 1) ^ (p - 1) = (p : Ω) * (w : A).1 at hw'
    rw [hw', ← map_natCast (algebraMap O Ω) p, ← hu, map_mul]
    change (algebraMap Kv Ω (tameUniformizer v).1 *
      algebraMap O Ω (u : O) * (w : A).1) / _ = _
    rw [mul_assoc, mul_div_cancel_left₀]
    · rfl
    · exact (map_ne_zero (algebraMap Kv Ω)).mpr (by
        intro h; exact tameUniformizer_ne_zero v (Subtype.ext h))
  let z : A := ⟨(completionZeta p - 1) / tameUniformizerRoot v,
    IsIntegral.of_pow (Nat.sub_pos_of_lt hp.out.one_lt) (by
      rw [hpow]; exact (w' : A).2)⟩
  have hz : z ^ (p - 1) = w' := Subtype.ext hpow
  have hunit : IsUnit z := (isUnit_pow_iff (Nat.sub_pos_of_lt hp.out.one_lt).ne').mp
    (hz ▸ w'.isUnit)
  exact ⟨hunit.unit, congrArg Subtype.val hunit.unit_spec⟩

/-- Inertia fixes the correcting unit, leaving precisely the cyclotomic ratio. -/
theorem residue_kummerRatioIntegral (σ : localInertiaGroup v) :
    residue A (kummerRatioIntegral v σ) =
      (((inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p).val : ResidueField A) := by
  let a := ((inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p).val
  let s : A := ∑ j ∈ Finset.range a, completionZetaIntegral p ^ j
  have hζ : completionZeta p ≠ 1 := (completionZeta_spec p).ne_one hp.out.one_lt
  have hs := map_cyclotomic_ratio (residue A) (algebraMap A Ω) hζ
    (residue_completionZetaIntegral p) a
  have hσ : σ.1 (completionZeta p) = completionZeta p ^ a := by
    have h := (completionZeta_spec p).autToPow_spec Kv σ.1
    rw [(completionZeta_spec p).autToPow_eq_modularCyclotomicCharacter p Kv σ.1] at h
    exact h.symm
  obtain ⟨z, hz⟩ := exists_unit_cyclotomic_root_ratio p
  have hzinv : ((z⁻¹ : Aˣ) : A).1 = ((completionZeta p - 1) / tameUniformizerRoot v)⁻¹ := by
    rw [← hz]
    apply eq_inv_of_mul_eq_one_right
    exact congrArg (fun x : A ↦ x.1) (Units.mul_inv z)
  have hratio : s = (σ.1 • (z : A)) * ((z⁻¹ : Aˣ) : A) * kummerRatioIntegral v σ := by
    apply Subtype.ext
    change s.1 = σ.1 (z : A).1 * ((z⁻¹ : Aˣ) : A).1 *
      (σ.1 (tameUniformizerRoot v) / tameUniformizerRoot v)
    rw [hz, hzinv]
    rw [show s.1 = (completionZeta p ^ a - 1) / (completionZeta p - 1) from hs.1]
    rw [← hσ]
    simp only [map_div₀, map_sub, map_one]
    field_simp [tameUniformizerRoot_ne_zero v, sub_ne_zero.mpr hζ]
  have hres := congrArg (residue A) hratio
  simp only [map_mul, residue_smul_eq] at hres
  rw [← map_mul, Units.mul_inv, map_one, one_mul] at hres
  exact hres.symm.trans hs.2

/-- The tame character equals the local mod-p cyclotomic character. -/
theorem tameCharacter_eq_inertiaCharacter :
    (Units.mapEquiv (residueEquiv p).toMulEquiv).toMonoidHom.comp (tameCharacter v) =
      inertiaCharacter p := by
  ext σ
  change residueEquiv p (tameCharacter v σ : ResidueField O) =
    ((inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p)
  apply (residueEquiv p).symm.injective
  rw [RingEquiv.symm_apply_apply]
  apply (residueFieldMap v).injective
  have ht : residueFieldMap v (tameCharacter v σ : ResidueField O) =
      residue A (kummerRatioIntegral v σ) := by
    have h := (residueUnitsEquivRoots v).apply_symm_apply (reducedKummerCharacter v σ)
    exact congrArg (fun x : rootsOfUnity (Nat.card (ResidueField O) - 1) (ResidueField A) ↦
      ((x : (ResidueField A)ˣ) : ResidueField A)) h
  rw [ht, residue_kummerRatioIntegral]
  conv_rhs => rw [← ZMod.natCast_zmod_val ((inertiaCharacter p σ : (ZMod p)ˣ) : ZMod p)]
  rw [map_natCast, map_natCast]

end LocalCyclotomic
