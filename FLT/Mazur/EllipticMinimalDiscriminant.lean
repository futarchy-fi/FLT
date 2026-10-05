/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticWeightedScaling
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Minimality and integral weighted scaling

An integral change preserving the discriminant preserves minimality.
Weighted division by a nonzero element of the maximal ideal strictly
increases the multiplicative discriminant valuation, so a minimal equation
cannot have all five weighted coefficient depths.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A generic change between integral equations with equal discriminants preserves minimality. -/
theorem isMinimal_of_change_discriminant_eq (W V : WeierstrassCurve K)
    [IsMinimal R W] [IsIntegral R V] (C : VariableChange K)
    (hC : C • W = V) (hΔ : V.Δ = W.Δ) : IsMinimal R V := by
  have he : valuation_Δ_aux R V = valuation_Δ_aux R W := by
    apply Subtype.ext
    rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral, hΔ]
  constructor
  refine ⟨by simpa only [one_smul] using (inferInstance : IsIntegral R V), ?_⟩
  intro D hD hle
  have hi : IsIntegral R ((D * C) • W) := by simpa only [mul_smul, hC] using hD
  have hle' : valuation_Δ_aux R ((1 : VariableChange K) • W) ≤
      valuation_Δ_aux R ((D * C) • W) := by
    simpa only [one_smul, mul_smul, hC, he] using hle
  have hm := (IsMinimal.val_Δ_maximal (R := R) (W := W)).2 hi hle'
  simpa only [one_smul, mul_smul, hC, he] using hm

/-- Weighted division gives a strict improvement in discriminant valuation. -/
theorem weighted_discriminant_valuation_lt (W U : WeierstrassCurve R) {π : R}
    (hπm : π ∈ maximalIdeal R) (hU : U.Δ ≠ 0) (hΔ : W.Δ = π ^ 12 * U.Δ) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K W.Δ) <
      (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K U.Δ) := by
  let v := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  have hp : v (algebraMap R K π) < 1 :=
    ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem π).mpr hπm
  have hu : 0 < v (algebraMap R K U.Δ) := by
    apply pos_iff_ne_zero.mpr
    apply (Valuation.ne_zero_iff v).mpr
    exact fun hz => hU ((IsFractionRing.injective R K) (hz.trans (map_zero _).symm))
  change v _ < v _
  rw [hΔ, map_mul, map_pow, map_mul, map_pow]
  exact mul_lt_of_lt_one_left hu (pow_lt_one₀ zero_le hp (by decide : 12 ≠ 0))

/-- A generically elliptic minimal integral equation cannot admit integral weighted division. -/
theorem not_isMinimal_of_weighted_depths (W : WeierstrassCurve R)
    [(W.map (algebraMap R K)).IsElliptic] {π : R} (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal R) (h2 : W.a₂ ∈ maximalIdeal R ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal R ^ 3) (h4 : W.a₄ ∈ maximalIdeal R ^ 4)
    (h6 : W.a₆ ∈ maximalIdeal R ^ 6) : ¬ IsMinimal R (W.map (algebraMap R K)) := by
  intro hmin
  let := hmin
  obtain ⟨U, he1, he2, he3, he4, he6, hΔ⟩ :=
    exists_integral_weighted_model W hgen h1 h2 h3 h4 h6
  have hp : algebraMap R K π ≠ 0 := fun hz =>
    hπ ((IsFractionRing.injective R K) (hz.trans (map_zero _).symm))
  let C : VariableChange K := .mk (Units.mk0 (algebraMap R K π) hp) 0 0 0
  have hC : C • W.map (algebraMap R K) = U.map (algebraMap R K) :=
    weighted_model_variableChange _ W U hp he1 he2 he3 he4 he6
  have hU : U.Δ ≠ 0 := by
    intro hz
    apply (W.map (algebraMap R K)).isUnit_Δ.ne_zero
    simp [map_Δ, hΔ, hz]
  let : IsIntegral R (U.map (algebraMap R K)) := ⟨U, rfl⟩
  have ht : valuation_Δ_aux R (W.map (algebraMap R K)) <
      valuation_Δ_aux R (U.map (algebraMap R K)) := by
    change (valuation_Δ_aux R (W.map (algebraMap R K))).val <
      (valuation_Δ_aux R (U.map (algebraMap R K))).val
    rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral, map_Δ, map_Δ]
    exact weighted_discriminant_valuation_lt W U
      (hgen ▸ Ideal.mem_span_singleton_self π) hU hΔ
  have hi : IsIntegral R (C • W.map (algebraMap R K)) := hC ▸ inferInstance
  have hm := (IsMinimal.val_Δ_maximal (R := R) (W := W.map (algebraMap R K))).2 hi
    (by simpa only [one_smul, hC] using ht.le)
  exact (not_le_of_gt ht) (by simpa only [one_smul, hC] using hm)

/-- An integral variable change with u = 1 preserves minimality of the generic equation. -/
theorem isMinimal_integral_change_of_u_one (W : WeierstrassCurve R)
    [IsMinimal R (W.map (algebraMap R K))] (C : VariableChange R) (hu : C.u = 1) :
    IsMinimal R ((C • W).map (algebraMap R K)) := by
  let V := (C • W).map (algebraMap R K)
  let : IsIntegral R V := ⟨C • W, rfl⟩
  apply isMinimal_of_change_discriminant_eq (W.map (algebraMap R K)) V
    (C.map (algebraMap R K)) (map_variableChange ..)
  simp [V, map_Δ, variableChange_Δ, hu]

/-- An integral translation preserves minimality of the generic equation. -/
theorem isMinimal_integral_translation (W : WeierstrassCurve R)
    [IsMinimal R (W.map (algebraMap R K))] (r t : R) :
    IsMinimal R (((VariableChange.mk 1 r 0 t : VariableChange R) • W).map
      (algebraMap R K)) :=
  isMinimal_integral_change_of_u_one W (.mk 1 r 0 t) rfl

end FLT.Mazur
