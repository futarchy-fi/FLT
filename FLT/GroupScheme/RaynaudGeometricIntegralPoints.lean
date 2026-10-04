/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierPairing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Original geometric points extend to the actual integral closure -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- Restrict a specified original geometric point to integral coordinates. -/
def FF.restrictedPointCoordinate (X : FF R K) (x : X.Points) :
    X.CoordinateRing →ₐ[R] AlgebraicClosure K :=
  (X.pointCoordinate x).restrictScalars R |>.comp Algebra.TensorProduct.includeRight

/-- Every geometric point of a finite integral model has integral coordinate values. -/
theorem FF.restrictedPointCoordinate_integral (X : FF R K) (x : X.Points)
    (a : X.CoordinateRing) : IsIntegral R (X.restrictedPointCoordinate x a) :=
  (IsIntegral.of_finite R a).map (X.restrictedPointCoordinate x)

/-- The unique integral extension of the specified original point, without a lift assumption. -/
def FF.integralPointCoordinate (X : FF R K) (x : X.Points) :
    X.CoordinateRing →ₐ[R] integralClosure R (AlgebraicClosure K) :=
  (X.restrictedPointCoordinate x).codRestrict _ (X.restrictedPointCoordinate_integral x)

/-- The integral extension retains the original coordinate values. -/
@[simp] theorem FF.integralPointCoordinate_coe (X : FF R K) (x : X.Points)
    (a : X.CoordinateRing) :
    (X.integralPointCoordinate x a : AlgebraicClosure K) = X.pointCoordinate x (1 ⊗ₜ a) := rfl

/-- Integral extensions are unique because the actual integral closure embeds in the field. -/
theorem FF.integralPointCoordinate_unique (X : FF R K) (x : X.Points)
    (f : X.CoordinateRing →ₐ[R] integralClosure R (AlgebraicClosure K))
    (hf : ∀ a, (f a : AlgebraicClosure K) = X.pointCoordinate x (1 ⊗ₜ a)) :
    f = X.integralPointCoordinate x := by
  ext a
  exact hf a

/-- Integral extension commutes with the original integral coordinate morphisms. -/
theorem ModelHom.integralPointCoordinate_genericHom {X Y : FF R K} (f : ModelHom X Y)
    (x : X.Points) : Y.integralPointCoordinate (genericHom f x) =
      (X.integralPointCoordinate x).comp f.toAlgHom := by
  ext a
  change Y.pointCoordinate (genericHom f x) (1 ⊗ₜ a) = X.pointCoordinate x (1 ⊗ₜ f a)
  rw [ModelHom.pointCoordinate_genericHom]
  rfl

end ThreeAdicPlan
