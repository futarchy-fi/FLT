/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudGeometricIntegralPoints
public import FLT.GroupScheme.CartierTestBaseChange

/-! # Actual local Cartier characters over the integral closure and every test algebra -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
open HopfAlgebra.CartierDual
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- Extend the specified dual geometric point to a character on every integral test algebra. -/
def FF.integralCartierCharacter (X : FF R K) (y : X.cartierDual.Points)
    {S : Type} [CommRing S] [Algebra R S]
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) :
    WithConv (X.CoordinateRing →ₐ[R] S) →* Sˣ :=
  testCharacter (q.comp (X.cartierDual.integralPointCoordinate y))

/-- Evaluate the character on the unique integral extension of the original point. -/
def FF.integralCartierPairing (X : FF R K) (y : X.cartierDual.Points) (x : X.Points) :
    (integralClosure R (AlgebraicClosure K))ˣ :=
  X.integralCartierCharacter y (AlgHom.id _ _) (WithConv.toConv (X.integralPointCoordinate x))

/-- The extended character intertwines the same original transposed integral morphism. -/
theorem ModelHom.integralCartierCharacter_naturality {X Y : FF R K} (f : ModelHom X Y)
    (y : Y.cartierDual.Points) {S : Type} [CommRing S] [Algebra R S]
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (x : X.CoordinateRing →ₐ[R] S) :
    X.integralCartierCharacter (genericHom f.cartierDual y) q (WithConv.toConv x) =
      Y.integralCartierCharacter y q (WithConv.toConv (x.comp f.toAlgHom)) := by
  unfold FF.integralCartierCharacter
  rw [ModelHom.integralPointCoordinate_genericHom]
  exact testCharacter_naturality f (q.comp (Y.cartierDual.integralPointCoordinate y)) x

/-- Integral dual coordinates restrict the original generic dual coordinates. -/
theorem FF.integralDualCoordinate_generic (X : FF R K) (y : X.cartierDual.Points) :
    (integralClosure R (AlgebraicClosure K)).val.comp
      (X.cartierDual.integralPointCoordinate y) =
        testDualRestriction (X.dualPointCoordinate y) := by
  ext φ
  change X.cartierDual.pointCoordinate y (1 ⊗ₜ φ) =
    X.cartierDual.pointCoordinate y
      (X.cartierDualGenericEquiv.symm (X.cartierDualGenericEquiv (1 ⊗ₜ φ)))
  rw [BialgEquiv.symm_apply_apply]

/-- The integral extension specializes to exactly the specified original finite Cartier value. -/
theorem FF.integralCartierPairing_coe (X : FF R K) (y : X.cartierDual.Points) (x : X.Points) :
    ((X.integralCartierPairing y x : integralClosure R (AlgebraicClosure K)) :
      AlgebraicClosure K) = (X.cartierPairing y x : AlgebraicClosure K) := by
  change (integralClosure R (AlgebraicClosure K)).val
    (testEvaluation (X.cartierDual.integralPointCoordinate y)
      (X.integralPointCoordinate x).toLinearMap) = _
  erw [testEvaluation_coefficients]
  erw [X.integralDualCoordinate_generic y]
  change testEvaluation (testDualRestriction (X.dualPointCoordinate y))
    (X.restrictedPointCoordinate x).toLinearMap = _
  rw [FF.restrictedPointCoordinate, testEvaluation_baseChange]
  exact congrArg Units.val (testCharacter_eq_geometric (X.dualPointCoordinate y)
    (X.pointCoordinate x))

end ThreeAdicPlan
