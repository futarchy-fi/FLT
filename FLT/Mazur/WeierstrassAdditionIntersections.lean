/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineAdditionTransport
public import FLT.Mazur.WeierstrassVerticalChartCompatibility

/-!
# Concrete intersections of the four affine addition domains

Tensor over the common affine input product, retaining the original base algebra.
The spectra of these rings are the actual scheme intersections of the domains.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

instance additionChartAlgebra (i : AdditionChartIndex) : Algebra R (additionChartRing W i) :=
  match i with
  | .secant => inferInstanceAs (Algebra R (SecantChart W))
  | .tangent => inferInstanceAs (Algebra R (TangentChart W))
  | .verticalSecant => inferInstanceAs (Algebra R
      (ReciprocalTargetOpen W _ (verticalSecantSlope W)))
  | .verticalTangent => inferInstanceAs (Algebra R
      (ReciprocalTargetOpen W _ (verticalTangentSlope W)))

/-- The input restriction retains its algebra structure over the original base. -/
def additionChartAlgRestriction (i : AdditionChartIndex) :
    AffineProduct W →ₐ[R] additionChartRing W i :=
  match i with
  | .secant => secantRestriction W
  | .tangent => tangentRestriction W
  | .verticalSecant => verticalSecantRestriction W
  | .verticalTangent => verticalTangentRestriction W

/-- Forgetting the base algebra recovers the scheme-cover restriction. -/
theorem additionChartAlgRestriction_toRingHom (i : AdditionChartIndex) :
    (additionChartAlgRestriction W i).toRingHom = additionChartRestriction W i := by
  cases i <;> rfl

instance additionChartInputAlgebra (i : AdditionChartIndex) :
    Algebra (AffineProduct W) (additionChartRing W i) :=
  (additionChartAlgRestriction W i).toRingHom.toAlgebra

instance additionChartInputTower (i : AdditionChartIndex) :
    IsScalarTower R (AffineProduct W) (additionChartRing W i) :=
  IsScalarTower.of_algebraMap_eq' (additionChartAlgRestriction W i).comp_algebraMap.symm

/-- Coordinate ring of the intersection of two actual addition domains. -/
def AdditionIntersection (i j : AdditionChartIndex) :=
  additionChartRing W i ⊗[AffineProduct W] additionChartRing W j

instance (i j : AdditionChartIndex) : CommRing (AdditionIntersection W i j) :=
  inferInstanceAs (CommRing (_ ⊗[AffineProduct W] _))

instance (i j : AdditionChartIndex) : Algebra R (AdditionIntersection W i j) :=
  inferInstanceAs (Algebra R (_ ⊗[AffineProduct W] _))

instance (i j : AdditionChartIndex) :
    Algebra (AffineProduct W) (AdditionIntersection W i j) :=
  inferInstanceAs (Algebra (AffineProduct W) (_ ⊗[AffineProduct W] _))

instance (i j : AdditionChartIndex) :
    IsScalarTower R (AffineProduct W) (AdditionIntersection W i j) :=
  inferInstanceAs (IsScalarTower R (AffineProduct W) (_ ⊗[AffineProduct W] _))

/-- Restriction from the first domain to its intersection. -/
def additionIntersectionLeft (i j : AdditionChartIndex) :
    additionChartRing W i →ₐ[R] AdditionIntersection W i j :=
  Algebra.TensorProduct.includeLeft

/-- Restriction from the second domain to its intersection. -/
def additionIntersectionRight (i j : AdditionChartIndex) :
    additionChartRing W j →ₐ[R] AdditionIntersection W i j :=
  Algebra.TensorProduct.includeRight.restrictScalars R

/-- The two input pairs coincide in the tensor intersection. -/
theorem additionIntersection_inputs (i j : AdditionChartIndex) :
    (additionIntersectionLeft W i j).comp (additionChartAlgRestriction W i) =
      (additionIntersectionRight W i j).comp (additionChartAlgRestriction W j) := by
  apply AlgHom.ext
  intro x
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul x

/-- The concrete tensor spectrum is the actual scheme intersection. -/
theorem additionIntersection_isPullback (i j : AdditionChartIndex) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (additionIntersectionLeft W i j).toRingHom))
      (Spec.map (CommRingCat.ofHom (additionIntersectionRight W i j).toRingHom))
      (additionChartInclusion W i) (additionChartInclusion W j) := by
  apply isPullback_SpecMap_of_isPushout
  simp only [← additionChartAlgRestriction_toRingHom]
  exact CommRingCat.isPushout_tensorProduct (AffineProduct W)
    (additionChartRing W i) (additionChartRing W j)

/-- Explicit identification with the categorical fiber product. -/
def additionIntersectionPullbackIso (i j : AdditionChartIndex) :
    Spec (CommRingCat.of (AdditionIntersection W i j)) ≅
      pullback (additionChartInclusion W i) (additionChartInclusion W j) :=
  (additionIntersection_isPullback W i j).isoPullback

end FLT.Mazur.WeierstrassIntegralChart
