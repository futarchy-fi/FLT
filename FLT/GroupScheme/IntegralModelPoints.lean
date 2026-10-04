/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtension
public import FLT.GroupScheme.KummerPoints

/-!
# Integral-coordinate points of the specified finite-flat model

Restriction from the generic tensor algebra identifies the original point
module with algebra maps on integral coordinates, preserving morphisms and addition.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- Evaluate an original generic point on the integral coordinate ring. -/
def FF.integralPoints (X : FF R K) :
    X.Points ≃ (X.CoordinateRing →ₐ[R] AlgebraicClosure K) :=
  X.pointsEquiv.symm.toEquiv.trans
    ((Equiv.refl _).trans (Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing))

/-- Integral evaluation preserves the actual group law. -/
theorem FF.integralPoints_add (X : FF R K) (x y : X.Points) :
    X.integralPoints (x + y) =
      (Algebra.TensorProduct.lift (X.integralPoints x) (X.integralPoints y)
        (fun _ _ ↦ .all ..)).comp (Bialgebra.comulAlgHom R X.CoordinateRing) := by
  change Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing
    ((X.pointsEquiv.symm (x + y)).toMul) = _
  rw [map_add]
  exact Bialgebra.restrictPoints_mul _ _ _ _ _ _

/-- Integral evaluation commutes with the Galois action. -/
theorem FF.integralPoints_smul (X : FF R K)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : X.Points) :
    X.integralPoints (g • x) =
      (g.toAlgHom.restrictScalars R).comp (X.integralPoints x) := by
  change Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing
    ((X.inversePoints (g • x)).toMul) = _
  rw [map_smul]
  rfl

/-- Evaluating an integral morphism is exactly its prescribed generic map. -/
theorem integralPoints_genericHom {X Y : FF R K} (f : ModelHom X Y) (x : X.Points) :
    Y.integralPoints (genericHom f x) = (X.integralPoints x).comp f.toAlgHom := by
  change Bialgebra.restrictPoints R K (AlgebraicClosure K) Y.CoordinateRing
    ((Y.pointsEquiv.symm (Y.pointsEquiv
      (BialgHom.precompPoints f.baseChange (X.inversePoints x)))).toMul) = _
  rw [Y.pointsEquiv.symm_apply_apply]
  ext a
  rfl

end ThreeAdicPlan
