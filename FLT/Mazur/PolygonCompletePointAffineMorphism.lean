/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNormalizedPoles
public import FLT.Mazur.WeierstrassAffineEquationEvaluation

/-!
# The actual complement morphism to the normalized affine cubic

Evaluation in the normalized original functions gives a morphism from the
retained marked-point complement to its Weierstrass affine scheme. The
morphism respects the specified field square. No isomorphism is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Evaluate the actual affine coordinate ring in the normalized original functions. -/
def completeCartesianPointCoordinateEvaluation (i : Fin n) :
    (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing →+*
      Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤) :=
  WeierstrassAffineEquationEvaluation.evaluation
    (completeCartesianPointWeierstrass K n h L s p q hs i)
    (completeCartesianPointScalar K n h L s p q hs i)
    (completeCartesianPointNormalize K n h L s p q hs i
      (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)))
    (completeCartesianPointNormalize K n h L s p q hs i
      (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)))
    (completeCartesianPoint_weierstrassEquation K n h L s p q hs i)

/-- Evaluation retains exactly the prescribed field action. -/
theorem completeCartesianPointCoordinateEvaluation_scalars (i : Fin n) :
    (completeCartesianPointCoordinateEvaluation K n h L s p q hs i).comp
      (algebraMap L
        (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing) =
      completeCartesianPointScalar K n h L s p q hs i :=
  WeierstrassAffineEquationEvaluation.evaluation_comp_scalar ..

/-- The affine x generator evaluates to the original normalized pole-two function. -/
theorem completeCartesianPointCoordinateEvaluation_x (i : Fin n) :
    completeCartesianPointCoordinateEvaluation K n h L s p q hs i
      (algebraMap (Polynomial L)
        (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing
        Polynomial.X) =
      completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)) :=
  WeierstrassAffineEquationEvaluation.evaluation_x ..

/-- The affine y generator evaluates to the original normalized pole-three function. -/
theorem completeCartesianPointCoordinateEvaluation_y (i : Fin n) :
    completeCartesianPointCoordinateEvaluation K n h L s p q hs i
      (AdjoinRoot.root
        (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.polynomial) =
      completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) :=
  WeierstrassAffineEquationEvaluation.evaluation_y ..

/-- The original marked-point complement maps to the actual normalized affine cubic. -/
def completeCartesianPointToAffineCubic (i : Fin n) :
    (completeCartesianPointComplement K n h L s p q hs i).toScheme ⟶
      Spec (.of (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing) :=
  (completeCartesianPointComplement K n h L s p q hs i).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (completeCartesianPointCoordinateEvaluation K n h L s p q hs i))

/-- The complement morphism lies over the original specified base field. -/
theorem completeCartesianPointToAffineCubic_over (i : Fin n) :
    completeCartesianPointToAffineCubic K n h L s p q hs i ≫
      Spec.map (CommRingCat.ofHom (algebraMap L
        (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing)) =
      (completeCartesianPointComplement K n h L s p q hs i).ι ≫ q := by
  rw [completeCartesianPointToAffineCubic, Category.assoc, ← Spec.map_comp]
  change (completeCartesianPointComplement K n h L s p q hs i).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      ((completeCartesianPointCoordinateEvaluation K n h L s p q hs i).comp
      (algebraMap L
        (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing))) = _
  rw [completeCartesianPointCoordinateEvaluation_scalars]
  simp only [completeCartesianPointScalar, structureScalarMap, CommRingCat.ofHom_hom,
    Spec.map_comp]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
