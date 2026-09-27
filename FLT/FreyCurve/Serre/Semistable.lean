/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Basic
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Semistability of the integral Frey model

The discriminant and `c₄` never vanish simultaneously in a residue field.
This gives good or multiplicative reduction over discrete valuation rings.
-/

@[expose] public section

open FreyPackage WeierstrassCurve

/-- The integral Frey model has the usual polynomial formula for its `c₄` invariant. -/
theorem FreyCurve.c₄_int (P : FreyPackage) :
    P.freyCurveInt.c₄ = (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2 := by
  have h := congrArg WeierstrassCurve.c₄ (FreyCurve.map P)
  simp only [map_c₄, eq_intCast] at h
  exact_mod_cast h.trans (FreyCurve.c₄ P)

/-- The discriminant identity for the integral Frey model, with denominators cleared. -/
theorem FreyCurve.two_pow_eight_mul_Δ_int (P : FreyPackage) :
    2 ^ 8 * P.freyCurveInt.Δ = (P.a * P.b * P.c) ^ (2 * P.p) := by
  have h := congrArg WeierstrassCurve.Δ (FreyCurve.map P)
  simp only [map_Δ, eq_intCast] at h
  rw [FreyCurve.Δ] at h
  have h' : (2 : ℚ) ^ 8 * P.freyCurveInt.Δ = (P.a * P.b * P.c) ^ (2 * P.p) := by
    rw [h]
    ring
  exact_mod_cast h'

/-- The Frey discriminant and `c₄` cannot both vanish after mapping to a field. -/
theorem FreyCurve.map_c₄_ne_zero_of_map_Δ_eq_zero (P : FreyPackage) {F : Type*} [Field F]
    (f : ℤ →+* F)
    (hΔ : f P.freyCurveInt.Δ = 0) : f P.freyCurveInt.c₄ ≠ 0 := by
  by_cases h2 : (2 : F) = 0
  · have h4 : (4 : F) = 0 := by linear_combination 2 * h2
    have h24 : (24 : F) = 0 := by linear_combination 12 * h2
    simp [WeierstrassCurve.c₄, WeierstrassCurve.b₂, freyCurveInt, h4, h24]
  have hprod := congrArg f (FreyCurve.two_pow_eight_mul_Δ_int P)
  simp only [map_mul, map_pow, map_ofNat, hΔ, mul_zero] at hprod
  have hz : f P.a * f P.b * f P.c = 0 :=
    (pow_eq_zero_iff (mul_ne_zero two_ne_zero P.hp0)).mp hprod.symm
  have hab : IsCoprime (f P.a) (f P.b) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [gcd] using P.hgcdab)).map f
  have hac : IsCoprime (f P.a) (f P.c) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [gcd] using P.hgcdac)).map f
  rw [FreyCurve.c₄_int]
  simp only [map_add, map_mul, map_pow]
  rcases mul_eq_zero.mp hz with hab0 | hc0
  · rcases mul_eq_zero.mp hab0 with ha0 | hb0
    · have hb := hab.ne_zero_or_ne_zero.resolve_left (not_ne_iff.mpr ha0)
      simpa only [ha0, zero_pow P.hp0, zero_pow two_ne_zero, zero_mul, zero_add]
        using pow_ne_zero 2 (pow_ne_zero P.p hb)
    · have ha := hab.ne_zero_or_ne_zero.resolve_right (not_ne_iff.mpr hb0)
      simpa only [hb0, zero_pow P.hp0, zero_pow two_ne_zero, mul_zero, add_zero]
        using pow_ne_zero 2 (pow_ne_zero P.p ha)
  · have ha := hac.ne_zero_or_ne_zero.resolve_right (not_ne_iff.mpr hc0)
    have hflt := congrArg f P.hFLT
    simp only [map_add, map_pow, hc0, zero_pow P.hp0] at hflt
    have hb : f P.b ^ P.p = -(f P.a ^ P.p) := eq_neg_of_add_eq_zero_right hflt
    rw [hb]
    convert pow_ne_zero 2 (pow_ne_zero P.p ha) using 1
    ring

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

universe u

/-- The integral Frey equation has good or multiplicative reduction over every DVR. -/
theorem FreyCurve.good_or_multiplicative_integral (P : FreyPackage) (R K : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    let W := (P.freyCurveInt.map (algebraMap ℤ R)).baseChange K
    W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R := by
  dsimp only
  let W₀ := P.freyCurveInt.map (algebraMap ℤ R)
  let W := W₀.baseChange K
  have hInt : IsIntegral R W := ⟨W₀, rfl⟩
  let := hInt
  change W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R
  have hΔ : W.Δ = algebraMap R K W₀.Δ := W₀.map_Δ _
  have hc4 : W.c₄ = algebraMap R K W₀.c₄ := W₀.map_c₄ _
  by_cases hd : IsLocalRing.residue R W₀.Δ = 0
  · have hdmem : W₀.Δ ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.residue_eq_zero_iff _).mp hd
    have hc : IsLocalRing.residue R W₀.c₄ ≠ 0 := by
      simpa only [W₀, map_c₄, RingHom.comp_apply] using
        FreyCurve.map_c₄_ne_zero_of_map_Δ_eq_zero P
          ((IsLocalRing.residue R).comp (algebraMap ℤ R))
          (by simpa only [W₀, map_Δ, RingHom.comp_apply] using hd)
    have hcval : (maximalIdeal R).valuation K W.c₄ = 1 := by
      rw [hc4, valuation_eq_one_iff_notMem]
      exact fun h ↦ hc ((IsLocalRing.residue_eq_zero_iff _).mpr h)
    exact Or.inr {
      toIsMinimal := isMinimal_of_valuation_c₄_eq_one R W hcval
      badReduction := by rw [hΔ]; exact (valuation_lt_one_iff_mem _ _).mpr hdmem
      multiplicativeReduction := hcval }
  · have hdval : (maximalIdeal R).valuation K W.Δ = 1 := by
      rw [hΔ, valuation_eq_one_iff_notMem]
      exact fun h ↦ hd ((IsLocalRing.residue_eq_zero_iff _).mpr h)
    have hmin : IsMinimal R W := by
      refine ⟨⟨by simpa using hInt, ?_⟩⟩
      intro C hC _
      simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
        valuation_Δ_aux_eq_of_isIntegral R W, hdval]
      rw [← integralModel_Δ_eq R (C • W)]
      exact valuation_le_one _ _
    exact Or.inl { toIsMinimal := hmin, goodReduction := hdval }

/-- The rational Frey curve has good or multiplicative reduction after base change
to the fraction field of any discrete valuation ring, including at residue characteristic two. -/
theorem FreyPackage.good_or_multiplicative (P : FreyPackage) (R K : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra ℚ K] :
    (P.freyCurve.baseChange K).HasGoodReduction R ∨
      (P.freyCurve.baseChange K).HasMultiplicativeReduction R := by
  have hmodel : (P.freyCurveInt.map (algebraMap ℤ R)).baseChange K =
      P.freyCurve.baseChange K := by
    rw [← FreyCurve.map P]
    simp only [baseChange, map_map]
    congr 1
    exact Subsingleton.elim _ _
  simpa only [hmodel] using FreyCurve.good_or_multiplicative_integral P R K
