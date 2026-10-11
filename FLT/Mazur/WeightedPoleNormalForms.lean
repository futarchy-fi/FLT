/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeightedPoleMonomials
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Tactic.FinCases

/-!
# Quadratic normal forms and normalized weighted monomials

Pairs of exponents with y-degree at most one enumerate the ordered pole
monomials. Simultaneous scaling by a nonzero field scalar preserves their
independence, without any integrality assumption on the ambient ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeightedPoleMonomials

/-- Position of a monomial whose y exponent is zero or one. -/
def normalIndex (ab : ℕ × Fin 2) : ℕ :=
  if ab.2 = 0 then if ab.1 = 0 then 0 else 2 * ab.1 - 1 else 2 * ab.1 + 2

/-- The position recovers the original x exponent. -/
theorem xExponent_normalIndex (ab : ℕ × Fin 2) : xExponent (normalIndex ab) = ab.1 := by
  rcases ab with ⟨a, b⟩
  fin_cases b <;> simp only [normalIndex, xExponent] <;> split_ifs <;> omega

/-- The position recovers the original y exponent. -/
theorem yExponent_normalIndex (ab : ℕ × Fin 2) : yExponent (normalIndex ab) = ab.2.val := by
  rcases ab with ⟨a, b⟩
  fin_cases b <;> simp [normalIndex, yExponent]
  split_ifs <;> omega

/-- Distinct quadratic normal monomials occupy distinct positions. -/
theorem normalIndex_injective : Function.Injective normalIndex := by
  intro a b hab
  apply Prod.ext
  · simpa only [xExponent_normalIndex] using congrArg xExponent hab
  · exact Fin.ext (by simpa only [yExponent_normalIndex] using congrArg yExponent hab)

/-- Reading a quadratic normal monomial in the ordered sequence changes no function. -/
theorem monomial_normalIndex {A : Type*} [CommRing A] (x y : A) (ab : ℕ × Fin 2) :
    monomial x y (normalIndex ab) = x ^ ab.1 * y ^ ab.2.val := by
  simp only [monomial, xExponent_normalIndex, yExponent_normalIndex]

/-- Common coordinate scaling multiplies each monomial by its total-degree scalar. -/
theorem monomial_mul_coordinates {A : Type*} [CommRing A] (c x y : A) (j : ℕ) :
    monomial (c * x) (c * y) j = c ^ (xExponent j + yExponent j) * monomial x y j := by
  simp only [monomial, mul_pow, pow_add]
  ac_rfl

/-- Nonzero simultaneous coordinate scaling preserves independence of all monomials. -/
theorem linearIndependent_scaled {k A : Type*} [Field k] [CommRing A]
    (φ : k →+* A) (x y : A) (c : k) (hc : c ≠ 0)
    (hv : let _ := Module.compHom A φ; LinearIndependent k (monomial x y)) :
    let _ := Module.compHom A φ
    LinearIndependent k (monomial (φ c * x) (φ c * y)) := by
  let _ := Module.compHom A φ
  have hli := hv.units_smul (fun j ↦ Units.mk0 (c ^ (xExponent j + yExponent j))
    (pow_ne_zero _ hc))
  convert hli using 1
  funext j
  change monomial (φ c * x) (φ c * y) j =
    φ (c ^ (xExponent j + yExponent j)) * monomial x y j
  rw [map_pow, monomial_mul_coordinates]

/-- Independence of the ordered list implies independence in quadratic normal form. -/
theorem linearIndependent_normal {k A : Type*} [Field k] [CommRing A] [Module k A]
    (x y : A) (hv : LinearIndependent k (monomial x y)) :
    LinearIndependent k (fun ab : ℕ × Fin 2 ↦ x ^ ab.1 * y ^ ab.2.val) := by
  simpa only [Function.comp_def, monomial_normalIndex] using
    hv.comp normalIndex normalIndex_injective

end FLT.Mazur.WeightedPoleMonomials
