/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectivePointComparison

/-!
# The projective comparison preserves zero and negation

The infinity section is the classical zero point. On the affine chart the
constructed scheme negation is precisely homogeneous projective negation.
Every field point is either infinity or affine, giving the global comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- The classical zero point is the actual infinity section after coefficient extension. -/
theorem projectiveToIntegral_zero :
    (projectiveToIntegral W (0 : (W.map (algebraMap R K)).toProjective.Point)).left =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ integralCurveZero W := by
  rw [projectiveToIntegral_chart W 0 1 ![0, 1, 0] equation_zero rfl rfl]
  rw [integralCurveZero, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := K) W).toRingHom) ≫
    integralCurveChart W 1 = _
  rw [chartInfinityEvaluation_base]
  rfl

/-- A classical projective point is either infinity or a normalized affine point. -/
theorem projective_zero_or_affine (P : (W.map (algebraMap R K)).toProjective.Point) :
    P = 0 ∨ ∃ (x y : K) (h : (W.map (algebraMap R K)).toAffine.Nonsingular x y),
      P = Point.fromAffine (.some x y h) := by
  classical
  obtain ⟨A, rfl⟩ :=
    (Point.toAffineAddEquiv (W.map (algebraMap R K)).toProjective).symm.surjective P
  cases A with
  | zero => exact Or.inl rfl
  | some x y h => exact Or.inr ⟨x, y, h, rfl⟩

/-- The scheme negation evaluated on normalized affine coordinates is projective negation. -/
theorem integralChartPoint_negation_affine (v : Fin 3 → K)
    (hv : (W.map (algebraMap R K)).toProjective.Equation v) (hj : v 2 = 1)
    (hw : (W.map (algebraMap R K)).toProjective.Equation
      ((W.map (algebraMap R K)).toProjective.neg v)) :
    integralChartPoint W 2 v hv hj ≫ integralCurveNegation W =
      integralChartPoint W 2 ((W.map (algebraMap R K)).toProjective.neg v) hw hj := by
  rw [integralChartPoint, Category.assoc, integralCurveChart_negation_affine,
    ← Category.assoc, ← Spec.map_comp, integralChartPoint]
  have he : (evaluation W 2 v hv hj).comp (affineNegation W) =
      evaluation W 2 ((W.map (algebraMap R K)).toProjective.neg v) hw hj := by
    apply hom_ext
    intro i
    simp only [AlgHom.comp_apply, affineNegation_coord, evaluation_coord]
    have h := congrFun (chartNegationCoordinates_map W 2 (evaluation W 2 v hv hj)) i
    have heval : (evaluation W 2 v hv hj) ∘ coord W 2 = v :=
      funext (evaluation_coord W 2 v hv hj)
    rw [heval] at h
    simpa only [Function.comp_apply, evaluation_coord, WeierstrassCurve.Projective.neg] using h
  change Spec.map (CommRingCat.ofHom
    ((evaluation W 2 v hv hj).comp (affineNegation W)).toRingHom) ≫ _ = _
  exact congrArg (fun a : Coordinate W 2 →ₐ[R] K =>
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2) he

/-- The projective comparison intertwines classical negation and the actual global morphism. -/
theorem projectiveToIntegral_neg (P : (W.map (algebraMap R K)).toProjective.Point) :
    (projectiveToIntegral W (-P)).left =
      (projectiveToIntegral W P).left ≫ integralCurveNegation W := by
  rcases projective_zero_or_affine W P with rfl | ⟨x, y, h, rfl⟩
  · rw [neg_zero, projectiveToIntegral_zero, Category.assoc, integralCurveZero_negation]
  · let v : Fin 3 → K := ![x, y, 1]
    have hv : (W.map (algebraMap R K)).toProjective.Nonsingular v :=
      (nonsingular_some x y).mpr h
    have hn := nonsingular_neg hv
    rw [projectiveToIntegral_chart W (Point.fromAffine (.some x y h)) 2 v hv.left rfl rfl,
      projectiveToIntegral_chart W _ 2 _ hn.left rfl rfl]
    exact (integralChartPoint_negation_affine W v hv.left rfl hn.left).symm

end FLT.Mazur.WeierstrassIntegralChart
