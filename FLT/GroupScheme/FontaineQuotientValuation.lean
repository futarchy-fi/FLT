/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalDifferentValuation
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Valuations under approximate integral embeddings

A map from one finite three-adic extension's integers to another's integers
modulo a valuation ideal of cutoff greater than one preserves the valuation
of a uniformizer. This is the arithmetic input for pulling back smaller
cutoff ideals along approximate integral embeddings.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

omit [Algebra ℤ_[3] E] [IsScalarTower ℤ_[3] ℚ_[3] E] in
/-- A perturbation of strictly smaller spectral norm does not change the norm. -/
theorem spectralNorm_eq_of_sub_lt {x y : E}
    (h : spectralNorm ℚ_[3] E (x - y) < spectralNorm ℚ_[3] E y) :
    spectralNorm ℚ_[3] E x = spectralNorm ℚ_[3] E y := by
  have hneg : ∀ z : E, spectralNorm ℚ_[3] E (-z) = spectralNorm ℚ_[3] E z :=
    fun z ↦ spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic z)
  simpa only [sub_add_cancel] using
    isNonarchimedean_spectralNorm.add_eq_right_of_lt hneg h

omit [Algebra ℤ_[3] E] [IsScalarTower ℤ_[3] ℚ_[3] E]
  [FiniteDimensional ℚ_[3] E] in
/-- The spectral norm of three in every extension is `3⁻¹`. -/
theorem spectralNorm_three : spectralNorm ℚ_[3] E (3 : E) = (3 : ℝ)⁻¹ := by
  have h := spectralNorm_extends (K := ℚ_[3]) (L := E) (3 : ℚ_[3])
  have hp := Padic.norm_p (p := 3)
  norm_num only [Nat.cast_ofNat] at hp
  simpa only [map_ofNat, hp, one_div] using h

/-- Units modulo a proper valuation ideal lift to integral units. -/
theorem isUnit_of_quotient_isUnit {m : ℚ} (hm : 0 < m) (x : ThreeAdicIntegers E)
    (hx : IsUnit (Ideal.Quotient.mk (threeAdicValuationIdeal E m) x)) : IsUnit x := by
  let I := threeAdicValuationIdeal E m
  let : Nontrivial (ThreeAdicIntegers E ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (threeAdicValuationIdeal_ne_top E hm)
  let := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact IsLocalHom.map_nonunit x hx

variable (L : Type*) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- Modulo precision greater than one, any representative of the image of a
uniformizer has exactly the original uniformizer's spectral norm. -/
theorem spectralNorm_uniformizer_quotientMap {m : ℚ} (hm : 1 < m)
    (f : ThreeAdicIntegers L →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m)
    (π : ThreeAdicIntegers L) (hπ : Irreducible π) (y : ThreeAdicIntegers E)
    (hy : Ideal.Quotient.mk (threeAdicValuationIdeal E m) y = f π) :
    spectralNorm ℚ_[3] E (y : E) = spectralNorm ℚ_[3] L (π : L) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  let := spectralNorm.nontriviallyNormedField ℚ_[3] L
  have : CharZero (ThreeAdicIntegers L) := Algebra.charZero_of_charZero ℤ_[3] _
  let e := threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)})
  have he : e ≠ 0 := Nat.ne_of_gt (threeAdicIdealOrder_three_pos L)
  have hI3 : Ideal.span {(3 : ThreeAdicIntegers L)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  have hspan : Ideal.span {π ^ e} = Ideal.span {(3 : ThreeAdicIntegers L)} := by
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact (ideal_eq_maximalIdeal_pow_threeAdicIdealOrder L _ hI3).symm
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp hspan :
    Associated (π ^ e) (3 : ThreeAdicIntegers L))
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (f (u : ThreeAdicIntegers L))
  have hvunit : IsUnit v := isUnit_of_quotient_isUnit E (lt_trans zero_lt_one hm) v
    (hv ▸ u.isUnit.map f)
  have hvnorm : ‖(v : E)‖ = 1 := by
    obtain ⟨v', rfl⟩ := hvunit
    exact spectralNorm_unit E v'
  have hq : Ideal.Quotient.mk (threeAdicValuationIdeal E m) (y ^ e * v) =
      Ideal.Quotient.mk (threeAdicValuationIdeal E m) 3 := by
    rw [map_mul, map_pow, hy, hv, ← map_pow, ← map_mul, hu]
    simp only [map_ofNat]
  have hdiff := Ideal.Quotient.eq.mp hq
  change spectralNorm ℚ_[3] E ((y : E) ^ e * (v : E) - 3) ≤
    (3 : ℝ) ^ (-(m : ℝ)) at hdiff
  have hcut : (3 : ℝ) ^ (-(m : ℝ)) < spectralNorm ℚ_[3] E 3 := by
    rw [spectralNorm_three, ← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by exact_mod_cast neg_lt_neg hm)
  have hnorm := spectralNorm_eq_of_sub_lt E (hdiff.trans_lt hcut)
  change ‖(y : E) ^ e * (v : E)‖ = _ at hnorm
  rw [norm_mul, norm_pow, hvnorm, mul_one, spectralNorm_three] at hnorm
  have hsource := spectralNorm_eq_of_span_eq L hspan
  change ‖(π : L) ^ e‖ = spectralNorm ℚ_[3] L 3 at hsource
  rw [norm_pow, spectralNorm_three] at hsource
  exact (pow_left_inj₀ (norm_nonneg (y : E)) (norm_nonneg (π : L)) he).mp
    (hnorm.trans hsource.symm)

/-- An approximate embedding of precision greater than one preserves every
valuation cutoff at or below its precision, including its endpoint. -/
theorem mem_valuationIdeal_iff_of_quotientMap {m t : ℚ} (hm : 1 < m) (ht : t ≤ m)
    (f : ThreeAdicIntegers L →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m)
    (x : ThreeAdicIntegers L) (z : ThreeAdicIntegers E)
    (hz : Ideal.Quotient.mk (threeAdicValuationIdeal E m) z = f x) :
    z ∈ threeAdicValuationIdeal E t ↔ x ∈ threeAdicValuationIdeal L t := by
  by_cases hx : x = 0
  · subst x
    have hz0 : z ∈ threeAdicValuationIdeal E m :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hz.trans (map_zero f))
    exact iff_of_true (threeAdicValuationIdeal_antitone E ht hz0) (Ideal.zero_mem _)
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  let := spectralNorm.nontriviallyNormedField ℚ_[3] L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (ThreeAdicIntegers L)
  obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f π)
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (f (u : ThreeAdicIntegers L))
  have hvunit : IsUnit v := isUnit_of_quotient_isUnit E (lt_trans zero_lt_one hm) v
    (hv ▸ u.isUnit.map f)
  have hvnorm : ‖(v : E)‖ = 1 := by
    obtain ⟨v', rfl⟩ := hvunit
    exact spectralNorm_unit E v'
  have hynorm := spectralNorm_uniformizer_quotientMap E L hm f π hπ y hy
  have hnorm : spectralNorm ℚ_[3] E ((v * y ^ n : ThreeAdicIntegers E) : E) =
      spectralNorm ℚ_[3] L (x : L) := by
    have hxu' : (x : L) = ((u : ThreeAdicIntegers L) : L) * (π : L) ^ n := by
      exact_mod_cast hxu
    change ‖(v : E) * (y : E) ^ n‖ = ‖(x : L)‖
    rw [hxu', norm_mul, norm_pow, norm_mul, norm_pow, hvnorm, one_mul]
    change _ = spectralNorm ℚ_[3] L ((u : ThreeAdicIntegers L) : L) * _
    rw [spectralNorm_unit, one_mul]
    exact congrArg (fun a : ℝ ↦ a ^ n) hynorm
  have hw : v * y ^ n ∈ threeAdicValuationIdeal E t ↔
      x ∈ threeAdicValuationIdeal L t := by
    simp only [mem_threeAdicValuationIdeal, hnorm]
  have hq : Ideal.Quotient.mk (threeAdicValuationIdeal E m) z =
      Ideal.Quotient.mk (threeAdicValuationIdeal E m) (v * y ^ n) := by
    rw [hz, hxu, map_mul, map_pow, map_mul, map_pow, hv, hy]
  have hdiff : z - v * y ^ n ∈ threeAdicValuationIdeal E t :=
    threeAdicValuationIdeal_antitone E ht (Ideal.Quotient.eq.mp hq)
  constructor
  · intro hz'
    apply hw.mp
    simpa only [sub_sub_cancel] using (threeAdicValuationIdeal E t).sub_mem hz' hdiff
  · intro hx'
    simpa only [sub_add_cancel] using
      (threeAdicValuationIdeal E t).add_mem hdiff (hw.mpr hx')

/-- Pulling back a smaller quotient's zero ideal along an approximate
embedding gives exactly the corresponding valuation ideal in the source. -/
theorem ker_factor_comp_quotientMap {m t : ℚ} (hm : 1 < m) (ht : t ≤ m)
    (f : ThreeAdicIntegers L →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) :
    RingHom.ker ((Ideal.Quotient.factorₐ ℤ_[3]
      (threeAdicValuationIdeal_antitone E ht)).comp f).toRingHom =
        threeAdicValuationIdeal L t := by
  ext x
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (f x)
  rw [RingHom.mem_ker]
  change Ideal.Quotient.factorₐ ℤ_[3] (threeAdicValuationIdeal_antitone E ht) (f x) = 0 ↔ _
  rw [← hz]
  change Ideal.Quotient.mk (threeAdicValuationIdeal E t) z = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact mem_valuationIdeal_iff_of_quotientMap E L hm ht f x z hz

end ThreeAdicPlan
