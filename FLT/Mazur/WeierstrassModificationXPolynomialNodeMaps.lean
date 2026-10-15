/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeInverseFunctions
public import FLT.Mazur.NodalFiberAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Maps between the full initial arithmetic node neighborhoods

Both source and target retain the smoothing parameter s. Inverting q+a₁
includes the node intersection, and does not invert the incidence coordinate.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X])
local notation "A" => Coordinate W s b3 b4 b6
local notation "N" => NodalFiber.Coordinate s

/-- The node neighborhood selected by its opposite residue tangent. -/
abbrev PolynomialNodeOpen := Localization.Away (NodalFiber.q s + algebraMap R N W.a₁)

/-- The corresponding full original initial neighborhood, including t=0. -/
abbrev PolynomialInitialOpen := Localization.Away
  (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁)

local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r
local notation "P" => algebraMap N L (NodalFiber.p s)
local notation "Q" => algebraMap N L (NodalFiber.q s)

/-- The full node open retains its original smoothing parameter. -/
theorem polynomialNodeOpen_relation : P * Q = algebraMap R L s := by
  rw [← map_mul, NodalFiber.relation, ← IsScalarTower.algebraMap_apply R N L]

/-- The opposite tangent is a unit on the full node open by construction. -/
theorem polynomialNodeOpen_unit : IsUnit (Q + algebraMap R L W.a₁) := by
  simpa only [map_add, ← IsScalarTower.algebraMap_apply R N L] using
    IsLocalization.Away.algebraMap_isUnit (S := L) (NodalFiber.q s + algebraMap R N W.a₁)

variable (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)

/-- All original initial functions evaluated on the actual localized smoothing node. -/
def polynomialNodeForwardBase : A →ₐ[R] L :=
  polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 P Q
    (polynomialNodeOpen_unit W s) (polynomialNodeOpen_relation W s)

/-- The source denominator evaluates to the actual target denominator. -/
theorem polynomialNodeForwardBase_denominator :
    polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
      (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) =
        Q + algebraMap R L W.a₁ := by
  rw [map_add, AlgHom.commutes]
  change polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 P Q _ _ _ + _ = _
  rw [polynomialNodeEvaluation_small]

/-- The constructed inverse coordinates extend to the whole initial node neighborhood. -/
def polynomialNodeForward : O →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom
    (f := polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3)
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) (by
      rw [polynomialNodeForwardBase_denominator]
      exact polynomialNodeOpen_unit W s)

/-- The forward map agrees with the original initial evaluation on every function. -/
theorem polynomialNodeForward_base (z : A) :
    polynomialNodeForward W s b3 b4 b6 r hr I hI hrI h3 (algebraMap A O z) =
      polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3 z := by
  rw [polynomialNodeForward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX
