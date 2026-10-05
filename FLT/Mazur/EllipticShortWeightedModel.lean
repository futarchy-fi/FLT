/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticShortUnitReduction
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Integral short equations at the first unit coefficient

Dividing a short equation by a uniformizer to weights four and six is
integral under the corresponding valuation bounds. If either bound is an
equality, one divided coefficient is a unit, hence the new equation has
unit discriminant or unit c₄ when two and three are units.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Dividing off the full uniformizer valuation leaves a unit. -/
theorem isUnit_of_uniformizer_factor {ρ x c : R} (hρ : Irreducible ρ) (n : ℕ)
    (hx : x = ρ ^ n * c) (hv : addVal R x = (n : ℕ∞)) : IsUnit c := by
  apply addVal_eq_zero_iff.mp
  apply ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top n)
  change (n : ℕ∞) + addVal R c = (n : ℕ∞) + 0
  simpa only [hx, addVal_mul, hρ.addVal_pow, add_zero] using hv

/-- Integral short scaling with one saturated coefficient produces semistable invariants. -/
theorem exists_short_weighted_unit_model (W : WeierstrassCurve R)
    {ρ : R} (hρ : Irreducible ρ) (m : ℕ)
    (h4 : (4 * m : ℕ) ≤ addVal R W.a₄) (h6 : (6 * m : ℕ) ≤ addVal R W.a₆)
    (he : addVal R W.a₄ = (4 * m : ℕ) ∨ addVal R W.a₆ = (6 * m : ℕ))
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) :
    ∃ U : WeierstrassCurve R, U.IsShortNF ∧
      W.a₄ = (ρ ^ m) ^ 4 * U.a₄ ∧ W.a₆ = (ρ ^ m) ^ 6 * U.a₆ ∧
      (IsUnit U.Δ ∨ IsUnit U.c₄) := by
  obtain ⟨a, ha⟩ := addVal_le_iff_dvd.mp (by simpa only [hρ.addVal_pow] using h4 :
    addVal R (ρ ^ (4 * m)) ≤ addVal R W.a₄)
  obtain ⟨b, hb⟩ := addVal_le_iff_dvd.mp (by simpa only [hρ.addVal_pow] using h6 :
    addVal R (ρ ^ (6 * m)) ≤ addVal R W.a₆)
  let U : WeierstrassCurve R := ⟨0, 0, 0, a, b⟩
  have : U.IsShortNF := ⟨rfl, rfl, rfl⟩
  have hu : IsUnit U.a₄ ∨ IsUnit U.a₆ := by
    rcases he with he | he
    · exact Or.inl (isUnit_of_uniformizer_factor hρ (4 * m) ha he)
    · exact Or.inr (isUnit_of_uniformizer_factor hρ (6 * m) hb he)
  refine ⟨U, inferInstance, ?_, ?_, short_unit_discriminant_or_c₄ U h2 h3 hu⟩
  · simpa only [pow_mul, Nat.mul_comm] using ha
  · simpa only [pow_mul, Nat.mul_comm] using hb

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The divided short equation is related to the original by an actual generic scaling. -/
theorem short_weighted_model_variableChange {K : Type*} [Field K]
    (f : R →+* K) (W U : WeierstrassCurve R) [W.IsShortNF] [U.IsShortNF]
    {ρ : R} (hρ : f ρ ≠ 0) (m : ℕ)
    (h4 : W.a₄ = (ρ ^ m) ^ 4 * U.a₄) (h6 : W.a₆ = (ρ ^ m) ^ 6 * U.a₆) :
    (VariableChange.mk (Units.mk0 (f (ρ ^ m)) (by simpa using pow_ne_zero m hρ)) 0 0 0 :
      VariableChange K) • W.map f = U.map f := by
  apply weighted_model_variableChange f W U (by simpa using pow_ne_zero m hρ)
  · simp only [a₁_of_isShortNF, mul_zero]
  · simp only [a₂_of_isShortNF, mul_zero]
  · simp only [a₃_of_isShortNF, mul_zero]
  · exact h4
  · exact h6

end FLT.Mazur
