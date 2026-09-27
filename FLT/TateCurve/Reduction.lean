/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.JInvariant
public import FLT.KnownIn1980s.EllipticCurves.ReductionBaseChange

/-!
# Split multiplicative reduction of the Tate model

The coefficients a4 and a6 lie in the maximal ideal, while c4 is a unit and
the discriminant has valuation equal to that of q. The equation is minimal,
and its reduced node polynomial is `X * (X + 1)` in every residue characteristic.
-/

@[expose] public section

open ValuativeRel WeierstrassCurve
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- An integral series with zero constant coefficient evaluates into the maximal ideal. -/
theorem valuation_evalInt_lt_one {q : K} (hq : valuation K q < 1)
    {F : PowerSeries ℤ} (hF : PowerSeries.constantCoeff F = 0) :
    valuation K (evalInt q F) < 1 := by
  have h := valuation_evalInt_le_pow q hq (F := F) (M := 1) (by
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hF)
  exact h.trans_lt (by simpa using hq)

/-- The nonconstant coefficient a4 of a Tate curve vanishes in the residue field. -/
theorem valuation_tateA₄_lt_one {q : K} (hq : valuation K q < 1) :
    valuation K (tateA₄ q) < 1 := by
  rw [tateA₄_eq_evalInt q hq]
  exact valuation_evalInt_lt_one hq (by simp [a₄Formal, sInt])

/-- The nonconstant coefficient a6 of a Tate curve vanishes in the residue field. -/
theorem valuation_tateA₆_lt_one {q : K} (hq : valuation K q < 1) :
    valuation K (tateA₆ q) < 1 := by
  rw [tateA₆_eq_evalInt q hq]
  exact valuation_evalInt_lt_one hq (by simp [a₆Formal])

/-- The c4 invariant of the Tate equation is a unit. -/
theorem valuation_tateCurve_c₄ {q : K} (hq : valuation K q < 1) :
    valuation K (tateCurve q).c₄ = 1 := by
  have ha : valuation K ((48 : K) * tateA₄ q) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_left (valuation_natCast_le_one 48) _).trans_lt
      (by simpa using valuation_tateA₄_lt_one hq)
  have he : (tateCurve q).c₄ = 1 - 48 * tateA₄ q := by
    simp [tateCurve, WeierstrassCurve.c₄, b₂, b₄]
    ring
  rw [he, (valuation K).map_sub_eq_of_lt_left (by simpa using ha), map_one]

/-- The Tate equation has split multiplicative reduction on the punctured open unit disc. -/
theorem tateCurve_hasSplitMultiplicativeReduction {q : K} (hq0 : q ≠ 0)
    (hq : valuation K q < 1) : (tateCurve q).HasSplitMultiplicativeReduction 𝒪[K] := by
  let a4 : 𝒪[K] := ⟨tateA₄ q, (valuation_tateA₄_lt_one hq).le⟩
  let a6 : 𝒪[K] := ⟨tateA₆ q, (valuation_tateA₆_lt_one hq).le⟩
  let W : WeierstrassCurve 𝒪[K] := ⟨1, 0, 0, a4, a6⟩
  have hW : W.baseChange K = tateCurve q := by
    ext <;> simp [W, WeierstrassCurve.baseChange, WeierstrassCurve.map, tateCurve, a4, a6] <;> rfl
  let : IsIntegral 𝒪[K] (tateCurve q) := ⟨W, hW.symm⟩
  have hc4 : (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation K (tateCurve q).c₄ = 1 := by
    rw [← integralModel_c₄_eq 𝒪[K] (tateCurve q)]
    apply adicValuation_eq_one_iff.mpr
    rw [integralModel_c₄_eq]
    exact valuation_tateCurve_c₄ hq
  let : (tateCurve q).IsMinimal 𝒪[K] :=
    isMinimal_of_valuation_c₄_eq_one 𝒪[K] _ hc4
  have hd : (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation K (tateCurve q).Δ < 1 := by
    rw [← integralModel_Δ_eq 𝒪[K] (tateCurve q)]
    apply adicValuation_lt_one_iff.mpr
    rw [integralModel_Δ_eq, valuation_tateCurve_Δ hq0 hq]
    exact hq
  have hmodel : (tateCurve q).integralModel 𝒪[K] = W := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective 𝒪[K] K)
    exact (baseChange_integralModel_eq 𝒪[K] (tateCurve q)).trans hW.symm
  have hz (a : 𝒪[K]) (ha : valuation K (a : K) < 1) : IsLocalRing.residue 𝒪[K] a = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff a).mpr
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (mem_nonunits_iff.mpr (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr ha))
  have ha4 : IsLocalRing.residue 𝒪[K] a4 = 0 := hz _ (valuation_tateA₄_lt_one hq)
  have ha6 : IsLocalRing.residue 𝒪[K] a6 = 0 := hz _ (valuation_tateA₆_lt_one hq)
  refine {
    badReduction := hd
    multiplicativeReduction := hc4
    splitMultiplicativeReduction := ?_ }
  change Polynomial.Splits (Polynomial.map (IsLocalRing.residue 𝒪[K]) _)
  rw [hmodel]
  simp only [W, c₄, b₂, b₄, b₆, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_one, map_zero, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, ha4, ha6]
  norm_num
  have hp : (Polynomial.X ^ 2 + Polynomial.X : Polynomial (IsLocalRing.ResidueField 𝒪[K])) =
      Polynomial.X * (Polynomial.X + 1) := by ring
  rw [hp]
  exact Polynomial.Splits.mul Polynomial.Splits.X
    (by simpa using Polynomial.Splits.X_sub_C (-1 : IsLocalRing.ResidueField 𝒪[K]))
end TateCurve
