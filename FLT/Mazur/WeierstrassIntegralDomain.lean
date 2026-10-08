/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineChartDense
public import FLT.Mazur.WeierstrassAffineMonicComparison
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Integrality of the actual cubic over a domain

The monic affine model is a domain. The infinity chart embeds into the common
overlap, which is reduced as a localization of the affine model. Reducedness
therefore descends through the two-chart atlas, while density of the affine
chart gives irreducibility. No discriminant assumption is needed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [IsDomain R]

/-- The original affine coordinate quotient is a domain. -/
instance affineChart_isDomain : IsDomain (Coordinate W 2) :=
  (affineChartMonicEquiv W).toRingEquiv.toMulEquiv.isDomain _

/-- The infinity chart is reduced, by its injection into the affine overlap. -/
instance infinityChart_isReduced : _root_.IsReduced (Coordinate W 1) := by
  let _ : _root_.IsReduced (Overlap W 1 2) :=
    isReduced_of_injective (overlapEquiv W 2 1) (overlapEquiv W 2 1).injective
  exact isReduced_of_injective (overlapRestriction W 1 2)
    (infinityOverlapRestriction_injective W)

/-- Reducedness of the actual glued cubic over a domain. -/
instance integralCurve_isReduced : AlgebraicGeometry.IsReduced (integralCurve W) := by
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover _ (integralCurveTwoChartCover W)).mpr
  intro b
  cases b
  · change AlgebraicGeometry.IsReduced (chartScheme W 2)
    infer_instance
  · change AlgebraicGeometry.IsReduced (chartScheme W 1)
    infer_instance

/-- The dense integral affine chart makes the whole cubic irreducible. -/
instance integralCurve_irreducibleSpace : IrreducibleSpace (integralCurve W) := by
  rw [irreducibleSpace_def]
  have h := (IrreducibleSpace.isIrreducible_univ (chartScheme W 2)).image
    (integralCurveChart W 2) (integralCurveChart W 2).continuous.continuousOn
  rw [Set.image_univ] at h
  simpa only [(integralCurveAffine_denseRange W).closure_range, Set.top_eq_univ] using h.closure

/-- The actual projective Weierstrass cubic is integral over every domain. -/
instance integralCurve_isIntegral : AlgebraicGeometry.IsIntegral (integralCurve W) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- In particular the whole cubic is connected, including singular cubics. -/
theorem integralCurve_connectedSpace : ConnectedSpace (integralCurve W) := inferInstance

end FLT.Mazur.WeierstrassIntegralChart
