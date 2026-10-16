/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentMobiusGeometry
public import FLT.Mazur.WeierstrassModificationXZeroMobiusChart
public import FLT.Mazur.WeierstrassModificationXPolynomialNodeGeometry

/-!
# Full fractional coordinates on the original arithmetic initial neighborhood

The original polynomial root and divided coefficients are retained. The
fractional first coordinate includes the smoothing correction; the second
is the ratio of the original small factor to its opposite residue tangent.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ)
local notation "a" => zeroInitialTangentUnit W ha

/-- The entire original node open maps to its full fractionally normalized polygon chart. -/
def initialMobiusChart : Spec (.of (PolynomialNodeOpen W s)) ⟶
    PolygonSmoothing.chart R τ := NodalFiber.tangentMobiusChart s τ a hτ

instance initialMobiusChart_isOpenImmersion :
    IsOpenImmersion (initialMobiusChart W ha s τ hτ) :=
  NodalFiber.tangentMobiusChart_isOpenImmersion ..

/-- The original arithmetic coefficient structure is preserved by the full fractional chart. -/
@[reassoc] theorem initialMobiusChart_structure :
    initialMobiusChart W ha s τ hτ ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing τ))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (PolynomialNodeOpen W s))) :=
  NodalFiber.tangentMobiusChart_structure ..

variable (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r
local notation "M" => NodalFiber.TangentOpen τ (-1 : R)
local notation "g" => polynomialNodeBackward W s b3 b4 b6 r hr
local notation "V" => algebraMap A O (polynomialSmallFactor W s b3 b4 b6 r)

/-- Every original initial function has an inverse fractional coordinate expression. -/
def polynomialInitialMobiusEquiv : M ≃ₐ[R] O :=
  (NodalFiber.tangentMobiusEquiv s τ a hτ).trans
    (polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).symm

local notation "E" => polynomialInitialMobiusEquiv W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The first fractional coordinate retains the full original corrected incidence. -/
theorem polynomialInitialMobiusEquiv_p :
    E (NodalFiber.tangentP τ (-1 : R)) =
      algebraMap R O (↑a⁻¹ : R) *
        (algebraMap A O (t W s b3 b4 b6) *
          algebraMap A O (polynomialOppositeFactor W s b3 b4 b6 r)) + algebraMap R O τ := by
  change g (NodalFiber.tangentMobiusForward s τ a hτ _) = _
  rw [NodalFiber.tangentMobiusForward_p]
  change g (algebraMap R (PolynomialNodeOpen W s) (↑a⁻¹ : R) *
    algebraMap (NodalFiber.Coordinate s) (PolynomialNodeOpen W s) (NodalFiber.p s) +
      algebraMap R (PolynomialNodeOpen W s) τ) = _
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, polynomialNodeBackward_p]

/-- The full second coordinate is the fraction of the actual original small factor. -/
theorem polynomialInitialMobiusEquiv_q_denominator :
    E (NodalFiber.tangentQ τ (-1 : R)) * (V + algebraMap R O W.a₁) = V := by
  change g (NodalFiber.tangentMobiusForward s τ a hτ _) * _ = _
  rw [NodalFiber.tangentMobiusForward_q]
  have h := congrArg g (NodalFiber.tangentFraction_denominator s (a : R))
  change g (NodalFiber.tangentFraction s W.a₁ *
    (algebraMap (NodalFiber.Coordinate s) (PolynomialNodeOpen W s) (NodalFiber.q s) +
      algebraMap R (PolynomialNodeOpen W s) W.a₁)) =
        g (algebraMap (NodalFiber.Coordinate s) (PolynomialNodeOpen W s) (NodalFiber.q s)) at h
  rw [map_mul, map_add, AlgHom.commutes, polynomialNodeBackward_q] at h
  exact h

/-- The denominator equation identifies the fraction everywhere, including at the node. -/
theorem polynomialInitialMobiusEquiv_q :
    E (NodalFiber.tangentQ τ (-1 : R)) =
      V * ↑((polynomialInitialOpen_unit W s b3 b4 b6 r).unit⁻¹) := by
  apply (polynomialInitialOpen_unit W s b3 b4 b6 r).mul_right_cancel
  rw [polynomialInitialMobiusEquiv_q_denominator, mul_assoc,
    (polynomialInitialOpen_unit W s b3 b4 b6 r).val_inv_mul, mul_one]

end FLT.Mazur.WeierstrassModificationX
