/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionRelation

/-!
# Opposite smooth reductions add to infinity

If the sum of two integral affine points is integral, its slope is integral by
a monic quadratic equation. Two cleared slope identities then exclude opposite
smooth reductions, including reduced points of order two.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing Polynomial WeierstrassCurve

/-- The two cleared slope identities, valid also in the tangent chart. -/
theorem slope_cleared_identities {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F}
    (h₁ : E.toAffine.Equation x₁ y₁) (h₂ : E.toAffine.Equation x₂ y₂)
    (hxy : ¬ (x₁ = x₂ ∧ y₁ = E.toAffine.negY x₂ y₂)) :
    (x₁ - x₂) * E.toAffine.slope x₁ x₂ y₁ y₂ = y₁ - y₂ ∧
    (y₁ + y₂ + E.a₁ * x₂ + E.a₃) * E.toAffine.slope x₁ x₂ y₁ y₂ =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + E.a₂ * (x₁ + x₂) + E.a₄ - E.a₁ * y₁ := by
  by_cases hx : x₁ = x₂
  · have hy := fun hy => hxy ⟨hx, hy⟩
    have he := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    have hd : y₁ + y₂ + E.a₁ * x₂ + E.a₃ ≠ 0 := by
      intro hz
      apply hy
      simp only [Affine.negY]
      linear_combination hz
    rw [Affine.slope_eq_of_Y_ne E h₁ h₂ hy]
    constructor
    · simp only [hx, he, sub_self, zero_mul]
    · exact mul_div_cancel₀ _ hd
  · rw [Affine.slope_of_X_ne hx]
    constructor
    · exact mul_div_cancel₀ _ (sub_ne_zero.mpr hx)
    · apply (mul_right_cancel₀ (sub_ne_zero.mpr hx))
      field_simp
      have hp := (Affine.equation_iff _ _).mp h₁
      have hq := (Affine.equation_iff _ _).mp h₂
      linear_combination hp - hq

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

omit [DecidableEq K] in
/-- An integral addition x-coordinate forces an integral slope. -/
theorem slope_mem_of_addX_mem (x₁ x₂ : A) (l : K)
    (hr : (W.map (algebraMap A K)).toAffine.addX x₁ x₂ l ∈ A) : l ∈ A := by
  let r : A := ⟨_, hr⟩
  let f : A[X] := X ^ 2 + C W.a₁ * X - C (W.a₂ + x₁ + x₂ + r)
  have hf : f.Monic := by unfold f; monicity <;> norm_num
  have he : f.eval₂ (algebraMap A K) l = 0 := by
    simp only [f, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      map_add, ValuationSubring.algebraMap_apply]
    change l ^ 2 + (W.a₁ : K) * l - ((W.a₂ : K) + x₁ + x₂ +
      (W.map (algebraMap A K)).toAffine.addX x₁ x₂ l) = 0
    simp only [Affine.addX, map_a₁, map_a₂, ValuationSubring.algebraMap_apply]
    ring
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp (show IsIntegral A l from ⟨f, hf, he⟩)
  exact hb ▸ b.property

/-- An integral slope through integral points cannot join opposite smooth reductions. -/
theorem not_opposite_of_integral_slope (x₁ y₁ x₂ y₂ l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Equation x₁ y₁)
    (h₂ : (W.map (algebraMap A K)).toAffine.Equation x₂ y₂)
    (hr₁ : (W.map (residue A)).toAffine.Nonsingular (residue A x₁) (residue A y₁))
    (hxy : ¬ ((x₁ : K) = x₂ ∧ (y₁ : K) =
      (W.map (algebraMap A K)).toAffine.negY x₂ y₂))
    (hl : (W.map (algebraMap A K)).toAffine.slope x₁ x₂ y₁ y₂ = (l : K)) :
    ¬ (residue A x₁ = residue A x₂ ∧ residue A y₁ =
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂)) := by
  obtain ⟨hline, htan⟩ := slope_cleared_identities _ h₁ h₂ hxy
  rw [hl] at hline htan
  have hi : (x₁ - x₂) * l = y₁ - y₂ := by
    apply IsFractionRing.injective A K
    simpa only [map_mul, map_sub, ValuationSubring.algebraMap_apply] using hline
  have ht : (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * l =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ := by
    apply IsFractionRing.injective A K
    simpa only [map_mul, map_sub, map_add, map_pow, map_a₁, map_a₂, map_a₃, map_a₄,
      ValuationSubring.algebraMap_apply] using htan
  have hi' := congrArg (residue A) hi
  have ht' := congrArg (residue A) ht
  simp only [map_mul, map_sub, map_add, map_pow] at hi' ht'
  rintro ⟨hx, hy⟩
  have he : residue A y₁ = residue A y₂ := by
    apply sub_eq_zero.mp
    simpa only [hx, sub_self, zero_mul] using hi'.symm
  have hd : residue A y₁ + residue A y₂ + residue A W.a₁ * residue A x₂ +
      residue A W.a₃ = 0 := by
    simp only [Affine.negY, map_a₁, map_a₃] at hy
    linear_combination hy
  rw [hd, zero_mul] at ht'
  rcases (Affine.nonsingular_iff _ _).mp hr₁ with ⟨_, hns | hns⟩
  · apply hns
    simp only [map_a₁, map_a₂, map_a₄]
    rw [← hx] at ht'
    linear_combination ht'
  · apply hns
    simpa only [← hx, ← he, Affine.negY, map_a₁, map_a₃] using hy

/-- Opposite smooth affine reductions sum to the identity. -/
theorem reducesTo_add_of_residue_opposite (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₁ : K) (y₁ : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₂ : K) (y₂ : K))
    (hr₁ : (W.map (residue A)).toAffine.Nonsingular (residue A x₁) (residue A y₁))
    (hred : residue A x₁ = residue A x₂ ∧ residue A y₁ =
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂)) :
    ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) 0 := by
  by_cases hxy : (x₁ : K) = x₂ ∧ (y₁ : K) =
      (W.map (algebraMap A K)).toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact reducesTo_zero A W
  · rw [Affine.Point.add_some hxy]
    apply reducesTo_of_nonintegral
    intro hr
    have hl := slope_mem_of_addX_mem A W x₁ x₂ _ hr
    exact not_opposite_of_integral_slope A W x₁ y₁ x₂ y₂ ⟨_, hl⟩ h₁.1 h₂.1 hr₁ hxy
      rfl hred

end FLT.Mazur
