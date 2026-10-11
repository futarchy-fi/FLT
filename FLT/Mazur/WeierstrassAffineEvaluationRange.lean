/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineEvaluationInjective
public import FLT.Mazur.WeightedPoleNormalForms

/-!
# The range of actual affine coordinate evaluation

Evaluation has the span of the normal monomials as its range. When the
coordinates were simultaneously scaled by a nonzero field scalar, every
original monomial is still in that same range.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassAffineEquationEvaluation
open Polynomial Module
variable {k A : Type*} [Field k] [CommRing A]
  (W : WeierstrassCurve k) (φ : k →+* A) (x y : A)

/-- The range consists exactly of the linear combinations of normal monomials. -/
theorem evaluationLinear_range (he : (W.map φ).toAffine.Equation x y) :
    let _ := Module.compHom A φ
    (evaluationLinear W φ x y he).range =
      Submodule.span k (Set.range (fun ab : ℕ × Fin 2 ↦ x ^ ab.1 * y ^ ab.2.val)) := by
  let _ := Module.compHom A φ
  have hb := (normalBasis W).constr_range (S := k)
    (f := fun ab ↦ evaluationLinear W φ x y he (normalBasis W ab))
  rw [Basis.constr_self] at hb
  simpa only [evaluationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    evaluation_normalBasis] using hb

/-- Any monomial in the evaluated coordinates belongs to the actual evaluation range. -/
theorem monomial_mem_evaluation_range (he : (W.map φ).toAffine.Equation x y) (a b : ℕ) :
    let _ := Module.compHom A φ
    x ^ a * y ^ b ∈ (evaluationLinear W φ x y he).range := by
  let _ := Module.compHom A φ
  refine ⟨algebraMap k[X] W.toAffine.CoordinateRing X ^ a *
    AdjoinRoot.root W.toAffine.polynomial ^ b, ?_⟩
  simp only [evaluationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    map_mul, map_pow, evaluation_x, evaluation_y]

/-- Inverting the normalization scalar recovers every original ordered monomial. -/
theorem originalMonomial_mem_evaluation_range (c : k) (hc : c ≠ 0)
    (he : (W.map φ).toAffine.Equation (φ c * x) (φ c * y)) (j : ℕ) :
    let _ := Module.compHom A φ
    WeightedPoleMonomials.monomial x y j ∈
      (evaluationLinear W φ (φ c * x) (φ c * y) he).range := by
  let _ := Module.compHom A φ
  apply (Submodule.smul_mem_iff _
    (pow_ne_zero (WeightedPoleMonomials.xExponent j + WeightedPoleMonomials.yExponent j)
      hc)).mp
  change φ (c ^ _) * WeightedPoleMonomials.monomial x y j ∈ _
  rw [map_pow, ← WeightedPoleMonomials.monomial_mul_coordinates]
  exact monomial_mem_evaluation_range W φ (φ c * x) (φ c * y) he _ _

end FLT.Mazur.WeierstrassAffineEquationEvaluation
