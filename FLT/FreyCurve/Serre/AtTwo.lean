/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.Semistable
public import Mathlib.NumberTheory.Padics.LocalField

/-!
# Multiplicative reduction of the Frey curve at two

The integral discriminant is even. Together with the unit `c₄` invariant,
this gives multiplicative reduction in residue characteristic two.
-/

@[expose] public section

open FreyPackage WeierstrassCurve

/-- The discriminant of the normalized integral Frey model is even. -/
theorem FreyCurve.two_dvd_Δ_int (P : FreyPackage) : 2 ∣ P.freyCurveInt.Δ := by
  have hb : (2 : ℤ) ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).mp P.hb2
  have hp : (2 : ℤ) ^ 9 ∣ (P.a * P.b * P.c) ^ (2 * P.p) :=
    (pow_dvd_pow_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb _) _) 9).trans
      (pow_dvd_pow _ (by have := P.hp5; omega))
  rw [← FreyCurve.two_pow_eight_mul_Δ_int P] at hp
  have heq : (2 : ℤ) ^ 9 = 2 ^ 8 * 2 := by norm_num
  rw [heq] at hp
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ^ 8 ≠ 0)).mp hp

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

universe u

/-- The Frey curve has multiplicative reduction over a DVR of residue characteristic two. -/
theorem FreyCurve.hasMultiplicativeReduction_of_two_eq_zero (P : FreyPackage) (R K : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra ℚ K]
    (h2 : (2 : IsLocalRing.ResidueField R) = 0) :
    (P.freyCurve.baseChange K).HasMultiplicativeReduction R := by
  let W₀ := P.freyCurveInt.map (algebraMap ℤ R)
  let W := W₀.baseChange K
  have hmodel : W = P.freyCurve.baseChange K := by
    rw [← FreyCurve.map P]
    simp only [W, W₀, baseChange, map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [← hmodel]
  have hInt : IsIntegral R W := ⟨W₀, rfl⟩
  let := hInt
  have hd : IsLocalRing.residue R W₀.Δ = 0 := by
    obtain ⟨d, hd⟩ := FreyCurve.two_dvd_Δ_int P
    simp only [W₀, map_Δ, eq_intCast, hd,
      map_mul, map_ofNat, h2, zero_mul]
  have hc : IsLocalRing.residue R W₀.c₄ ≠ 0 := by
    simpa only [W₀, map_c₄, RingHom.comp_apply] using
      FreyCurve.map_c₄_ne_zero_of_map_Δ_eq_zero P
        ((IsLocalRing.residue R).comp (algebraMap ℤ R))
        (by simpa only [W₀, map_Δ, RingHom.comp_apply] using hd)
  have hcval : (maximalIdeal R).valuation K W.c₄ = 1 := by
    rw [show W.c₄ = algebraMap R K W₀.c₄ from W₀.map_c₄ _,
      valuation_eq_one_iff_notMem]
    exact fun h ↦ hc ((IsLocalRing.residue_eq_zero_iff _).mpr h)
  exact {
    toIsMinimal := isMinimal_of_valuation_c₄_eq_one R W hcval
    badReduction := by
      rw [show W.Δ = algebraMap R K W₀.Δ from W₀.map_Δ _]
      exact (valuation_lt_one_iff_mem _ _).mpr
        ((IsLocalRing.residue_eq_zero_iff _).mp hd)
    multiplicativeReduction := hcval }

open ValuativeRel

/-- The Frey curve has multiplicative reduction over the two-adic field. -/
theorem FreyCurve.hasMultiplicativeReduction_at_two (P : FreyPackage) :
    (P.freyCurve.baseChange ℚ_[2]).HasMultiplicativeReduction 𝒪[ℚ_[2]] := by
  apply FreyCurve.hasMultiplicativeReduction_of_two_eq_zero P
  rw [← map_ofNat (IsLocalRing.residue 𝒪[ℚ_[2]]) 2,
    IsLocalRing.residue_eq_zero_iff]
  change ¬ IsUnit (2 : 𝒪[ℚ_[2]])
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact Padic.valuation_p_lt_one (ValuativeRel.valuation ℚ_[2])
