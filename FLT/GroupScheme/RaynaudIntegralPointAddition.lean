/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudGeometricIntegralPoints
public import FLT.GroupScheme.IntegralHopfPoints

/-! # Original point addition on the unique integral extensions -/

@[expose] public noncomputable section
open scoped TensorProduct
open Coalgebra
namespace ThreeAdicPlan
variable {R K S : Type} [CommRing R] [Field K] [Algebra R K]
  [CommRing S] [Algebra R S]

/-- Original geometric addition becomes convolution of the uniquely extended integral points. -/
theorem FF.integralPointCoordinate_add (X : FF R K) (x z : X.Points) :
    X.integralPointCoordinate (x + z) =
      (WithConv.toConv (X.integralPointCoordinate x) *
        WithConv.toConv (X.integralPointCoordinate z)).ofConv := by
  let f := (integralPointConvolution (R := R) (A := X.CoordinateRing)
    (B := AlgebraicClosure K) R).comp
      (genericPointConvolution R K (AlgebraicClosure K) X.CoordinateRing)
  have h := f.map_mul (X.pointCoordinate x) (X.pointCoordinate z)
  change f (X.pointCoordinate x * X.pointCoordinate z) = _ at h
  have he : X.pointCoordinate (x + z) = X.pointCoordinate x * X.pointCoordinate z := by
    unfold FF.pointCoordinate
    rw [map_add]
    rfl
  rw [← he] at h
  exact congrArg WithConv.ofConv h

/-- The integral extension of the original identity is the convolution identity. -/
theorem FF.integralPointCoordinate_zero (X : FF R K) :
    X.integralPointCoordinate 0 =
      (1 : WithConv (X.CoordinateRing →ₐ[R] integralClosure R (AlgebraicClosure K))).ofConv := by
  let f := (integralPointConvolution (R := R) (A := X.CoordinateRing)
    (B := AlgebraicClosure K) R).comp
      (genericPointConvolution R K (AlgebraicClosure K) X.CoordinateRing)
  have he : X.pointCoordinate 0 = 1 := by
    unfold FF.pointCoordinate
    rw [map_zero]
    rfl
  have h := f.map_one
  rw [← he] at h
  exact congrArg WithConv.ofConv h

/-- Coefficient specialization preserves convolution of integral test points. -/
theorem integralPointCoefficient_mul {A : Type} [CommRing A] [Bialgebra R A]
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (ψ χ : WithConv (A →ₐ[R] integralClosure R (AlgebraicClosure K))) :
    q.comp (ψ * χ).ofConv =
      (WithConv.toConv (q.comp ψ.ofConv) * WithConv.toConv (q.comp χ.ofConv)).ofConv := by
  ext a
  simp [AlgHom.convMul_apply, ← (ℛ R a).eq]

end ThreeAdicPlan
