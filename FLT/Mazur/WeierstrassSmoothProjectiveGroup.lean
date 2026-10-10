/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothNonoppositePoints
public import FLT.Mazur.WeierstrassSmoothGroup
public import FLT.Mazur.WeierstrassProjectivePointNegation

/-!
# The full smooth model has the classical projective point group

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
variable (W : WeierstrassCurve R)

/-- The projective comparison preserves every sum as an equality of actual scheme points. -/
theorem projectiveToSmoothOver_add (P Q : (W.map (algebraMap R K)).toProjective.Point) :
    projectiveToSmoothOver W (P + Q) =
      lift (projectiveToSmoothOver W P) (projectiveToSmoothOver W Q) ≫
        integralSmoothOverAddition W := by
  classical
  let _ := integralSmoothCommGrpObj W
  have hz : projectiveToSmoothOver W (0 : (W.map (algebraMap R K)).toProjective.Point) =
      (1 : smoothCurveFieldPoint (K := K) W) := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (integralSmoothOpen W).ι).mp
    change projectiveToSmooth W 0 ≫ _ =
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ integralSmoothZero W) ≫ _
    rw [projectiveToSmooth_inclusion, Category.assoc, integralSmoothZero_inclusion]
    exact projectiveToIntegral_zero W
  have hn (A : (W.map (algebraMap R K)).toProjective.Point) :
      projectiveToSmoothOver W (-A) = (projectiveToSmoothOver W A)⁻¹ := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (integralSmoothOpen W).ι).mp
    change projectiveToSmooth W (-A) ≫ _ =
      (projectiveToSmooth W A ≫ integralSmoothNegation W) ≫ _
    rw [projectiveToSmooth_inclusion, Category.assoc, integralSmoothNegation_inclusion,
      ← Category.assoc, projectiveToSmooth_inclusion]
    exact projectiveToIntegral_neg W A
  change projectiveToSmoothOver W (P + Q) = projectiveToSmoothOver W P * projectiveToSmoothOver W Q
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
  · exact projectiveToSmoothOver_add_nonopposite W h₁ h₂ h

/-- Field-valued points of the constructed model, with its proved group structure. -/
def smoothGroupFieldPoints : CommGrpCat :=
  CommGrpCat.of
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ (integralSmoothGroup W).X)

/-- The classical projective group is the field-point group of the constructed integral model. -/
def smoothProjectivePointAddEquiv :
    (W.map (algebraMap R K)).toProjective.Point ≃+
      Additive (smoothGroupFieldPoints (K := K) W) where
  toFun P := Additive.ofMul (projectiveToSmoothOver W P)
  invFun p := (smoothProjectivePointEquiv W).symm p.toMul
  left_inv := (smoothProjectivePointEquiv W).left_inv
  right_inv := (smoothProjectivePointEquiv W).right_inv
  map_add' := projectiveToSmoothOver_add W

/-- The group equivalence retains the original scheme morphism on every point. -/
theorem smoothProjectivePointAddEquiv_apply
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    (smoothProjectivePointAddEquiv W P).toMul = projectiveToSmoothOver W P := rfl

end FLT.Mazur.WeierstrassIntegralChart
