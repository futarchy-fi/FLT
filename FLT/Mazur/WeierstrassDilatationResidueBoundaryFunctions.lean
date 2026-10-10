/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueCoordinates
public import FLT.Mazur.NodalFiberBoundedParameterTransport

/-!
# Explicit horizontal functions on the two terminal residue normal forms

The whole original horizontal boundary is cut out by a₁⁻¹(cT⁻¹-T) at middle
depth, and by a₁⁻¹(y-x) on the oriented node before middle depth.
-/

@[expose] public noncomputable section
open IsLocalRing LaurentPolynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "a" => residueTangentUnit D
local notation "c" => residue R b6

/-- The original node comparison is the explicit constant transport after normalization. -/
theorem residueNodeEquiv_eq_constant (hp : 2 * k < n) :
    residueNodeEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp =
      (residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
        (NodalFiber.constantBoundedEquiv c 0
          ((residue_eq_zero_iff _).mpr (divided_constant_mem D k hp b6 h6))) := by
  rw [NodalFiber.constantBoundedEquiv_def]
  rfl

/-- The original Laurent comparison transports the unit witness of the actual constant. -/
theorem residueLaurentEquiv_eq_cast (hp : 2 * k = n) :
    residueLaurentEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp =
      (residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
        (NodalFiber.unitLaurentBoundedCast
          ((divided_constant_isUnit D k hp b6 h6).map (residue R)).unit c
          ((divided_constant_isUnit D k hp b6 h6).map (residue R)).unit_spec) := by
  rw [NodalFiber.unitLaurentBoundedCast_def]
  rfl

/-- Before middle depth the horizontal generator retains the ordered tangent difference. -/
theorem residueNodeEquiv_x (hp : 2 * k < n) :
    residueNodeEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
      (tensorX W (π ^ k) b3 b4 b6 K) =
        algebraMap K _ (↑(a)⁻¹ : K) * (NodalFiber.q 0 - NodalFiber.p 0) := by
  rw [residueNodeEquiv_eq_constant, AlgEquiv.trans_apply, residueFiberEquiv_x,
    map_mul, map_sub, AlgEquiv.commutes, NodalFiber.constantBoundedEquiv_q,
    NodalFiber.constantBoundedEquiv_p]

/-- The first tangent coordinate remains the original vertical generator on the node. -/
theorem residueNodeEquiv_y (hp : 2 * k < n) :
    residueNodeEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
      (tensorY W (π ^ k) b3 b4 b6 K) = NodalFiber.p 0 := by
  rw [residueNodeEquiv_eq_constant, AlgEquiv.trans_apply, residueFiberEquiv_y,
    NodalFiber.constantBoundedEquiv_p]

/-- The normalized node denominator uses both ordered branch coordinates. -/
@[simp] theorem residuePolygonEquiv_x (hp : 2 * k < n) :
    residuePolygonEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
      (tensorX W (π ^ k) b3 b4 b6 K) =
        algebraMap K _ (↑(a)⁻¹ : K) *
          (PolygonNodeLocalization.y - PolygonNodeLocalization.x) := by
  rw [residuePolygonEquiv, AlgEquiv.trans_apply, residueNodeEquiv_x,
    map_mul, map_sub, AlgEquiv.commutes,
    NodalFiber.polygonNodeEquiv_q, NodalFiber.polygonNodeEquiv_p]

/-- The normalized node keeps the first tangent orientation. -/
@[simp] theorem residuePolygonEquiv_y (hp : 2 * k < n) :
    residuePolygonEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
      (tensorY W (π ^ k) b3 b4 b6 K) = PolygonNodeLocalization.x := by
  rw [residuePolygonEquiv, AlgEquiv.trans_apply, residueNodeEquiv_y,
    NodalFiber.polygonNodeEquiv_p]

/-- At middle depth the normalized denominator is a₁⁻¹(cT⁻¹-T), with the actual c. -/
@[simp] theorem residueLaurentEquiv_x (hp : 2 * k = n) :
    residueLaurentEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
      (tensorX W (π ^ k) b3 b4 b6 K) =
        C (↑(a)⁻¹ : K) * (C c * T (-1) - T 1) := by
  rw [residueLaurentEquiv_eq_cast, AlgEquiv.trans_apply, residueFiberEquiv_x,
    map_mul, map_sub, AlgEquiv.commutes, NodalFiber.unitLaurentBoundedCast_q,
    NodalFiber.unitLaurentBoundedCast_p]
  rfl

/-- The Laurent parameter is the original vertical divided coordinate. -/
@[simp] theorem residueLaurentEquiv_y (hp : 2 * k = n) :
    residueLaurentEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
      (tensorY W (π ^ k) b3 b4 b6 K) = T 1 := by
  rw [residueLaurentEquiv_eq_cast, AlgEquiv.trans_apply, residueFiberEquiv_y,
    NodalFiber.unitLaurentBoundedCast_p]

end FLT.Mazur.WeierstrassDilatation
