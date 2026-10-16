/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberZeroTangentMobiusPuncture
public import FLT.Mazur.WeierstrassModificationXNodeOverlapFactorRatioCoordinates
public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioBoundary

/-!
# Both actual original overlap legs have exact reciprocal polygon boundaries

The corrected whole-node open immersion now restricts along the original two
legs to the same full Laurent parameter, with inversion on the reflected leg.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialNodeOverlap W s
local notation "H" => polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "u" => polynomialNodeOverlapRatio W s b3 b4 b6 r hr I hI hrI h3
local notation "D" => polynomialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "C" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The exact common parameter on the entire actual original overlap scheme. -/
def factorRatioOverlapParameter : Spec (.of O) ⟶ PolygonSmoothing.branchTorus R :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) u).toRingHom)

local notation "P" => factorRatioOverlapParameter W s b3 b4 b6 r hr I hI hrI h3

/-- The first full original overlap leg factors through the corrected polygon right edge. -/
@[reassoc] theorem polynomialFactorRatioChart_overlap_first :
    polynomialNodeOverlapInclusion W s ≫ C = P ≫ PolygonSmoothing.rightBranchOpen R τ := by
  rw [polynomialFactorRatioChart_eq_spec, polynomialNodeOverlapInclusion, ← Spec.map_comp]
  apply PolygonSmoothing.boundary_rightBranchOpen τ ((Algebra.algHom R L O).comp D) u
  rw [AlgHom.comp_apply, polynomialFactorRatioEvaluation_right]
  exact polynomialFactorRatioMap_overlap_q W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- Actual original reflection gives exact edge inversion in the complete arithmetic square. -/
@[reassoc] theorem polynomialFactorRatioChart_overlap_opposite :
    polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 ≫ C =
      P ≫ (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.rightBranchOpen R τ := by
  rw [polynomialNodeOverlapOpposite_eq_spec]
  have h : Spec.map (CommRingCat.ofHom (H).toRingHom) ≫ C =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) (u)⁻¹).toRingHom) ≫
        PolygonSmoothing.rightBranchOpen R τ := by
    rw [polynomialFactorRatioChart_eq_spec, ← Spec.map_comp]
    apply PolygonSmoothing.boundary_rightBranchOpen τ ((H).comp D) (u)⁻¹
    rw [AlgHom.comp_apply, polynomialFactorRatioEvaluation_right]
    exact polynomialFactorRatioMap_overlap_opposite_q W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
  rw [NodalFiber.unitParameter_inverse, Category.assoc] at h
  exact h

end FLT.Mazur.WeierstrassModificationX
