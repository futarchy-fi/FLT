/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassGeometricFourTorsion

/-!
# Nonzero field points lie in the original affine chart

This records factorization of the actual field-valued scheme morphism,
using the original comparison with classical elliptic points.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [DecidableEq K]
  (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- A classical affine point factors through chart Z = 1 of the original cubic. -/
theorem affinePoint_factor {x y : K} (h : (W.map (algebraMap R K)).toAffine.Nonsingular x y) :
    ∃ q : Spec (.of K) ⟶ chartScheme W 2,
      q ≫ integralCurveChart W 2 =
        ((integralAffinePointAddEquiv W hΔ (.some x y h)).toMul).left := by
  let v : Fin 3 → K := ![x, y, 1]
  have hv : (W.map (algebraMap R K)).toProjective.Nonsingular v :=
    (Projective.nonsingular_some x y).mpr h
  refine ⟨Spec.map (CommRingCat.ofHom (evaluation W 2 v hv.left rfl).toRingHom), ?_⟩
  exact (projectiveToIntegral_chart W (Projective.Point.fromAffine (.some x y h))
    2 v hv.left rfl rfl).symm

omit [DecidableEq K] in
/-- Every nonidentity field point of the original group factors through the affine chart. -/
theorem nonzeroPoint_factor (P : integralGroupFieldPoints (K := K) W hΔ) (hP : P ≠ 1) :
    ∃ q : Spec (.of K) ⟶ chartScheme W 2, q ≫ integralCurveChart W 2 = P.left := by
  classical
  obtain ⟨A, hA⟩ := (integralAffinePointAddEquiv (K := K) W hΔ).surjective
    (Additive.ofMul P)
  cases A with
  | zero =>
    exact (hP (congrArg Additive.toMul (hA.symm.trans (map_zero _)))).elim
  | some x y h =>
    obtain ⟨q, hq⟩ := affinePoint_factor W hΔ h
    exact ⟨q, hq.trans (congrArg (fun p ↦ (Additive.toMul p).left) hA)⟩

end FLT.Mazur.WeierstrassIntegralChart
