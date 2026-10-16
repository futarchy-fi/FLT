/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroNodeOverlapFractions
public import FLT.Mazur.NodalFiberZeroTangentMobiusPuncture

/-!
# Exact full geometric overlap boundaries of the original fractional charts

Both legs of the original full initial-node intersection factor through the
polygon right puncture. Their Laurent parameters are the original tangent
ratio and its reciprocal, with the original coefficient ring unchanged.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local notation "L" => PolynomialNodeOpen W 0
local notation "O" => PolynomialNodeOverlap W 0
local notation "v" => polynomialNodeOverlapRatio W 0 b3 b4 b6 r hr I hI hrI h3

/-- The original full intersection's exact Laurent parameter, before orientation. -/
def zeroMobiusOverlapParameter : Spec (.of O) ⟶ PolygonSmoothing.branchTorus R :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) v).toRingHom)

include hbot

/-- The first full original restriction reaches the right puncture with its actual ratio. -/
@[reassoc] theorem zeroInitialMobiusChart_overlap_first :
    polynomialNodeOverlapInclusion W 0 ≫ zeroInitialMobiusChart W ha =
      zeroMobiusOverlapParameter W b3 b4 b6 r hr I hI hrI h3 ≫
        PolygonSmoothing.rightBranchOpen R 0 := by
  exact NodalFiber.zeroTangentMobiusChart_second_boundary (zeroInitialTangentUnit W ha)
    (Algebra.algHom R L O) v
    (polynomialZeroNodeOverlap_fraction W b3 b4 b6 r hr I hI hrI h3 hbot)

/-- The actual opposite restriction reaches the right puncture with the reciprocal parameter. -/
@[reassoc] theorem zeroInitialMobiusChart_overlap_opposite :
    polynomialNodeOverlapOpposite W 0 b3 b4 b6 r hr I hI hrI h3 ≫
      zeroInitialMobiusChart W ha =
        zeroMobiusOverlapParameter W b3 b4 b6 r hr I hI hrI h3 ≫
          (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.rightBranchOpen R 0 := by
  rw [polynomialNodeOverlapOpposite_eq_spec]
  have h := NodalFiber.zeroTangentMobiusChart_second_boundary (zeroInitialTangentUnit W ha)
    (polynomialNodeOverlapOppositeEvaluation W 0 b3 b4 b6 r hr I hI hrI h3) (v)⁻¹
    (polynomialZeroNodeOverlap_opposite_fraction W b3 b4 b6 r hr I hI hrI h3 hbot)
  rw [NodalFiber.unitParameter_inverse, Category.assoc] at h
  exact h

end FLT.Mazur.WeierstrassModificationX
