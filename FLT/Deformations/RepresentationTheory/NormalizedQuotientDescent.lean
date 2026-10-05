/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Descent of a normalized rank-one quotient

A unit eigenvalue gap at one element determines a normalized quotient row.
An injective coefficient map then descends its equivariance at every element.
-/

@[expose] public noncomputable section
namespace Deformation

variable {A B G : Type*} [CommRing A] [CommRing B]

/-- The last row of a recovery frame is an eigenrow before conjugation. -/
theorem recoveryFrame_eigenrow (P M N : GL (Fin 2) B) (c : B)
    (h : P * M * P⁻¹ = N) (hn : ∀ j, N 1 j = if j = 1 then c else 0)
    (j : Fin 2) : P 1 0 * M 0 j + P 1 1 * M 1 j = c * P 1 j := by
  have he : P * M = N * P := by rw [← h]; simp [mul_assoc]
  have hj := congrArg (fun X : GL (Fin 2) B ↦ X 1 j) he
  change (P.val * M.val) 1 j = (N.val * P.val) 1 j at hj
  simpa [Matrix.mul_apply, Fin.sum_univ_two, hn] using hj

/-- A separated eigenvalue descends the entire normalized quotient, not just one matrix. -/
theorem exists_normalizedQuotient_descent (f : A →+* B) (hf : Function.Injective f)
    (M : G → Matrix (Fin 2) (Fin 2) A) (χ : G → A) (a b : B)
    (hb : IsUnit b) (he : ∀ g j, a * f (M g 0 j) + b * f (M g 1 j) = f (χ g) *
      (if j = 0 then a else b)) (g₀ : G) (hd : IsUnit (M g₀ 0 0 - χ g₀)) :
    ∃ t : A, f t * b = a ∧
      ∀ g j, t * M g 0 j + M g 1 j = χ g * (if j = 0 then t else 1) := by
  obtain ⟨d, hd⟩ := hd
  let t := -M g₀ 1 0 * (↑d⁻¹ : A)
  have ht : t * (M g₀ 0 0 - χ g₀) = -M g₀ 1 0 := by
    rw [← hd]
    simp [t, mul_assoc]
  have hta : f t * b = a := by
    apply (d.isUnit.map f).mul_right_cancel
    have h₀ := he g₀ 0
    simp only [↓reduceIte] at h₀
    have ht' := congrArg f ht
    simp only [map_mul, map_sub, map_neg] at ht'
    rw [hd, map_sub]
    linear_combination b * ht' - h₀
  refine ⟨t, hta, fun g j ↦ hf ?_⟩
  apply hb.mul_left_cancel
  have hj := he g j
  fin_cases j
  · simp only [Fin.isValue, Fin.zero_eta, map_add, map_mul, ↓reduceIte] at hj ⊢
    rw [← hta] at hj
    linear_combination hj
  · simp only [Fin.isValue, Fin.mk_one, map_add, map_mul, one_ne_zero, ↓reduceIte,
      mul_one] at hj ⊢
    rw [← hta] at hj
    linear_combination hj

/-- The same unit gap makes the normalized quotient independent of every choice. -/
theorem normalizedQuotient_unique (M : Matrix (Fin 2) (Fin 2) A) (c t u : A)
    (hd : IsUnit (M 0 0 - c))
    (ht : t * M 0 0 + M 1 0 = c * t)
    (hu : u * M 0 0 + M 1 0 = c * u) : t = u := by
  apply hd.mul_right_cancel
  linear_combination ht - hu

/-- The normalized row defines a surjective functional without freeness assumptions. -/
def normalizedQuotient (t : A) : (Fin 2 → A) →ₗ[A] A where
  toFun x := t * x 0 + x 1
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

/-- The second coordinate supplies a section of the normalized functional. -/
theorem normalizedQuotient_surjective (t : A) : Function.Surjective (normalizedQuotient t) := by
  intro y
  exact ⟨![0, y], by simp [normalizedQuotient]⟩

/-- Row equivariance gives equivariance on the original free module. -/
theorem normalizedQuotient_equivariant (t c : A) (M : Matrix (Fin 2) (Fin 2) A)
    (h : ∀ j, t * M 0 j + M 1 j = c * (if j = 0 then t else 1)) (x : Fin 2 → A) :
    normalizedQuotient t (M.mulVec x) = c * normalizedQuotient t x := by
  have h₀ := h 0
  have h₁ := h 1
  simp at h₀ h₁
  simp only [normalizedQuotient, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  linear_combination x 0 * h₀ + x 1 * h₁

end Deformation
