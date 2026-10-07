/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionIntersections
public import FLT.Mazur.WeierstrassInputPolynomialScaling

/-!
# Coordinate rings of the transported affine addition domains

Tensor the simultaneous input overlap with an affine addition domain over its
normalized affine input pair. The spectrum is the actual transported domain,
and its original homogeneous inputs scale to the normalized affine inputs.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k : Fin 3)

instance productOverlapAffineAlgebra : Algebra (AffineProduct W) (ProductOverlap W j k 2 2) :=
  (productOverlapOther W j k 2 2).toRingHom.toAlgebra

instance productOverlapAffineTower :
    IsScalarTower R (AffineProduct W) (ProductOverlap W j k 2 2) :=
  IsScalarTower.of_algebraMap_eq' (productOverlapOther W j k 2 2).comp_algebraMap.symm

variable (i : AdditionChartIndex)

/-- The actual base change of an affine addition domain to the input overlap. -/
def TransportedAdditionRing := ProductOverlap W j k 2 2 ⊗[AffineProduct W] additionChartRing W i

instance : CommRing (TransportedAdditionRing W j k i) :=
  inferInstanceAs (CommRing (_ ⊗[AffineProduct W] _))

instance : Algebra R (TransportedAdditionRing W j k i) :=
  inferInstanceAs (Algebra R (_ ⊗[AffineProduct W] _))

/-- Restriction of the simultaneous input overlap to the transported domain. -/
def transportedAdditionOverlap : ProductOverlap W j k 2 2 →ₐ[R]
    TransportedAdditionRing W j k i := Algebra.TensorProduct.includeLeft

/-- The transported domain retains the original affine addition functions. -/
def transportedAdditionAffine : additionChartRing W i →ₐ[R]
    TransportedAdditionRing W j k i := Algebra.TensorProduct.includeRight.restrictScalars R

/-- The normalized affine inputs agree in the transported tensor ring. -/
theorem transportedAdditionRing_inputs :
    (transportedAdditionOverlap W j k i).comp (productOverlapOther W j k 2 2) =
      (transportedAdditionAffine W j k i).comp (additionChartAlgRestriction W i) := by
  apply AlgHom.ext
  intro a
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul
    (R := AffineProduct W) (A := ProductOverlap W j k 2 2) (B := additionChartRing W i) a

/-- The ring spectrum is the actual pullback defining a transported addition domain. -/
theorem transportedAdditionRing_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (transportedAdditionOverlap W j k i).toRingHom))
      (Spec.map (CommRingCat.ofHom (transportedAdditionAffine W j k i).toRingHom))
      (affineInputOverlapMap W j k) (additionChartInclusion W i) := by
  apply isPullback_SpecMap_of_isPushout
  simp only [← additionChartAlgRestriction_toRingHom]
  exact CommRingCat.isPushout_tensorProduct (AffineProduct W)
    (ProductOverlap W j k 2 2) (additionChartRing W i)

/-- The spectrum identifies with the already constructed transported cover member. -/
def transportedAdditionRingIso (hΔ : IsUnit W.Δ) :
    Spec (CommRingCat.of (TransportedAdditionRing W j k i)) ≅
      (affineOverlapAdditionCover W j k hΔ).X i :=
  (transportedAdditionRing_isPullback W j k i).isoPullback

/-- The original, unnormalized input pair on the transported domain. -/
def transportedAdditionInput : ChartProduct W j k →ₐ[R] TransportedAdditionRing W j k i :=
  (transportedAdditionOverlap W j k i).comp (productOverlapRestriction W j k 2 2)

/-- Unit relating the polynomial outputs before and after input normalization. -/
def transportedAdditionScale : TransportedAdditionRing W j k i :=
  transportedAdditionOverlap W j k i (productOverlapAdditionScale W j k 2 2)

/-- The input normalization factor stays invertible on every transported domain. -/
theorem transportedAdditionScale_isUnit : IsUnit (transportedAdditionScale W j k i) :=
  (productOverlapAdditionScale_isUnit W j k 2 2).map (transportedAdditionOverlap W j k i)

/-- The transported polynomial outputs obey the concrete input-scaling identity. -/
theorem transportedAdditionPolynomial_scaled (a : Fin 3) :
    transportedAdditionAffine W j k i
        (additionChartAlgRestriction W i (chartProductAdditionCoordinates W 2 2 a)) =
      transportedAdditionScale W j k i *
        transportedAdditionInput W j k i (chartProductAdditionCoordinates W j k a) := by
  refine (DFunLike.congr_fun (transportedAdditionRing_inputs W j k i)
    (chartProductAdditionCoordinates W 2 2 a)).symm.trans ?_
  change transportedAdditionOverlap W j k i
    (productOverlapOther W j k 2 2 (chartProductAdditionCoordinates W 2 2 a)) = _
  rw [productOverlap_addition_scaled, map_mul]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
