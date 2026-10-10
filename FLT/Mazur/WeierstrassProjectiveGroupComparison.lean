/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNonoppositeOrdinaryLift
public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# The integral model has the classical projective point group

Ordinary charts handle every nonopposite affine pair. The proved identity and
inverse laws handle infinity and opposite pairs. Thus the field-point
comparison preserves addition everywhere, and gives an isomorphism of groups.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory
open WeierstrassCurve WeierstrassCurve.Projective
open scoped MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The projective comparison preserves every sum as an equality of actual scheme points. -/
theorem projectiveToIntegral_add (P Q : (W.map (algebraMap R K)).toProjective.Point) :
    projectiveToIntegral W (P + Q) =
      lift (projectiveToIntegral W P) (projectiveToIntegral W Q) ≫
        integralCurveOverAddition W hΔ := by
  classical
  let _ := integralCurveCommGrpObj W hΔ
  have hz : projectiveToIntegral W (0 : (W.map (algebraMap R K)).toProjective.Point) =
      (1 : integralCurveFieldPoint (K := K) W) := by
    apply Over.OverMorphism.ext
    exact projectiveToIntegral_zero W
  have hn (A : (W.map (algebraMap R K)).toProjective.Point) :
      projectiveToIntegral W (-A) = (projectiveToIntegral W A)⁻¹ := by
    apply Over.OverMorphism.ext
    exact projectiveToIntegral_neg W A
  change projectiveToIntegral W (P + Q) = projectiveToIntegral W P * projectiveToIntegral W Q
  rcases projective_zero_or_affine W P with rfl | ⟨x₁, y₁, h₁, rfl⟩
  · rw [zero_add, hz, one_mul]
  rcases projective_zero_or_affine W Q with rfl | ⟨x₂, y₂, h₂, rfl⟩
  · rw [add_zero, hz, mul_one]
  by_cases h : x₁ = x₂ ∧ y₁ = (W.map (algebraMap R K)).toAffine.negY x₂ y₂
  · have heA : Affine.Point.some x₁ y₁ h₁ = -(Affine.Point.some x₂ y₂ h₂) := by
      rw [Affine.Point.neg_some]
      obtain ⟨rfl, hy⟩ := h
      cases hy
      rfl
    have he := congrArg (Point.toAffineAddEquiv (W.map (algebraMap R K)).toProjective).symm heA
    rw [map_neg] at he
    change Point.fromAffine (.some _ _ h₁) = -Point.fromAffine (.some _ _ h₂) at he
    rw [he, neg_add_cancel, hz, hn, inv_mul_cancel]
  · exact projectiveToIntegral_add_nonopposite W hΔ h₁ h₂ h

/-- Field-valued points of the constructed model, with its proved group structure. -/
def integralGroupFieldPoints : CommGrpCat :=
  CommGrpCat.of
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ (integralCurveGroup W hΔ).X)

/-- The classical projective group is the field-point group of the constructed integral model. -/
def integralProjectivePointAddEquiv :
    (W.map (algebraMap R K)).toProjective.Point ≃+
      Additive (integralGroupFieldPoints (K := K) W hΔ) where
  toFun P := Additive.ofMul (projectiveToIntegral W P)
  invFun p := (integralProjectivePointEquiv W hΔ).symm p.toMul
  left_inv := (integralProjectivePointEquiv W hΔ).left_inv
  right_inv := (integralProjectivePointEquiv W hΔ).right_inv
  map_add' := projectiveToIntegral_add W hΔ

/-- The group equivalence retains the original scheme morphism on every point. -/
theorem integralProjectivePointAddEquiv_apply
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    (integralProjectivePointAddEquiv W hΔ P).toMul = projectiveToIntegral W P := rfl

end FLT.Mazur.WeierstrassIntegralChart
