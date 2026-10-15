/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstDefectDerivation
public import FLT.Mazur.PolygonCompleteIdentityFirstPrincipalCoordinates
public import FLT.Mazur.PolygonNodeScalarExtension

/-!
# Computing the original action defect on every node function

The two normalization polynomials reconstruct every reduced node function.
Applying the actual coefficient derivation gives an explicit formula using
only their derivatives and the two original coordinate errors. This removes
the arbitrary function lift from all evaluations of the original obstruction.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing Polynomial PolygonNodeEqualizer LaurentNodePrincipalParts
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField

/-- The original quotient node is reconstructed by its two actual normalization polynomials. -/
theorem splitNode_polynomial_reconstruct (R : Type) [CommRing R] (z : ChartRing (0 : R)) :
    aeval (leftCoordinate (0 : R)) (first (specialFiberEquiv R z)) +
      aeval (rightCoordinate (0 : R)) (second (specialFiberEquiv R z)) -
      algebraMap R (ChartRing (0 : R)) ((first (specialFiberEquiv R z)).eval 0) = z := by
  apply (specialFiberEquiv R).injective
  simp only [map_sub, map_add, ← aeval_algHom_apply, specialFiberEquiv_left,
    specialFiberEquiv_right, AlgEquiv.commutes]
  exact PolygonNodeScalarExtension.reconstruct _

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "N" => ChartRing (0 : R)
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0
local notation "Q" => completeIdentityFirstReciprocalError K n h i
local notation "D" => completeIdentityFirstDefectCoefficient K n h i
local notation "A" => completeIdentityFirstReducedScaling K

/-- The actual original coefficient defect on a polynomial in any node function. -/
theorem completeIdentityFirstDefectCoefficient_aeval (p : (R)[X]) (z : N) :
    (D) (aeval z p) = (A) (aeval z p.derivative) * (D) z := by
  let _ := (A).toRingHom.toAlgebra
  exact (completeIdentityFirstDefectDerivation K n h i).map_aeval p z

/-- The original full coefficient defect is computed from two actual polynomial derivatives. -/
theorem completeIdentityFirstDefectCoefficient_formula (z : N) :
    (D) z =
      (A) (aeval (leftCoordinate (0 : R))
        (first (specialFiberEquiv (R) z)).derivative) * ((O), 0) +
      (A) (aeval (rightCoordinate (0 : R))
        (second (specialFiberEquiv (R) z)).derivative) * (0, (Q)) := by
  have he := congrArg (D) (splitNode_polynomial_reconstruct (R) z)
  rw [map_sub, map_add, completeIdentityFirstDefectCoefficient_scalar, sub_zero,
    completeIdentityFirstDefectCoefficient_aeval, completeIdentityFirstDefectCoefficient_aeval,
    completeIdentityFirstDefectCoefficient_left, completeIdentityFirstDefectCoefficient_right] at he
  exact he.symm

/-- The concrete principal obstruction on every function has a formula with no selected lift. -/
theorem completeIdentityFirstPrincipalObstruction_formula (z : N) :
    completeIdentityFirstPrincipalObstruction K n h i z = principalParts
      ((A) (aeval (leftCoordinate (0 : R))
          (first (specialFiberEquiv (R) z)).derivative) * ((O), 0) +
        (A) (aeval (rightCoordinate (0 : R))
          (second (specialFiberEquiv (R) z)).derivative) * (0, (Q))) := by
  change principalParts ((D) z) = _
  rw [completeIdentityFirstDefectCoefficient_formula]

end FLT.Mazur.PolygonInfinitesimalStages
