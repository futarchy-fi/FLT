/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialNodeMaps

/-!
# The original initial functions give the reverse node map

The corrected incidence and the small factor have product s on the full
initial neighborhood. They define the reverse map on every node function.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
local notation "A" => Coordinate W s b3 b4 b6
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r
local notation "ι" => algebraMap A O
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r
local notation "V" => polynomialSmallFactor W s b3 b4 b6 r

include hr in
/-- The original corrected incidence and small factor retain their smoothing product. -/
theorem polynomialInitialOpen_relation : (ι (t W s b3 b4 b6) * ι U) * ι V =
    algebraMap R O s := by
  have h := congrArg ι (polynomialFactors_incidence W s b3 b4 b6 r hr)
  rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply R A O] at h
  linear_combination h

/-- The original opposite residue tangent is a unit on the selected initial open. -/
theorem polynomialInitialOpen_unit : IsUnit (ι V + algebraMap R O W.a₁) := by
  simpa only [map_add, ← IsScalarTower.algebraMap_apply R A O] using
    IsLocalization.Away.algebraMap_isUnit (S := O) (V + algebraMap R A W.a₁)

/-- The original incidence solves precisely the inverse parameter equation. -/
theorem polynomialInitialOpen_parameter :
    ι (t W s b3 b4 b6) * (ι V + algebraMap R O W.a₁ +
      (r.eval₂ (algebraMap R O) (ι (t W s b3 b4 b6)) +
        r.eval₂ (algebraMap R O) (ι (t W s b3 b4 b6)) +
          algebraMap R O b3 * ι (t W s b3 b4 b6))) = ι (t W s b3 b4 b6) * ι U := by
  let g : A →ₐ[R] O := Algebra.algHom R A O
  change g (t W s b3 b4 b6) * (g V + algebraMap R O W.a₁ +
    (r.eval₂ (algebraMap R O) (g (t W s b3 b4 b6)) +
      r.eval₂ (algebraMap R O) (g (t W s b3 b4 b6)) +
        algebraMap R O b3 * g (t W s b3 b4 b6))) = g (t W s b3 b4 b6) * g U
  simp only [polynomialSmallFactor, polynomialOppositeFactor, map_sub, map_add]
  rw [hom_polynomial_incidence, hom_polynomial_incidence]
  simp only [polynomialSlopeLinear, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  ring

/-- The original functions define the reverse map on the entire smoothing node algebra. -/
def polynomialNodeBackwardBase : N →ₐ[R] O :=
  NodalFiber.evaluation s (ι (t W s b3 b4 b6) * ι U) (ι V)
    (polynomialInitialOpen_relation W s b3 b4 b6 r hr)

/-- The reverse map sends the first node coordinate to the full corrected incidence. -/
@[simp] theorem polynomialNodeBackwardBase_p :
    polynomialNodeBackwardBase W s b3 b4 b6 r hr (NodalFiber.p s) =
      ι (t W s b3 b4 b6) * ι U := NodalFiber.evaluation_p ..

/-- The reverse map sends the second node coordinate to the full small factor. -/
@[simp] theorem polynomialNodeBackwardBase_q :
    polynomialNodeBackwardBase W s b3 b4 b6 r hr (NodalFiber.q s) = ι V :=
  NodalFiber.evaluation_q ..

/-- The reverse map extends to the actual node neighborhood. -/
def polynomialNodeBackward : L →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (f := polynomialNodeBackwardBase W s b3 b4 b6 r hr)
    (NodalFiber.q s + algebraMap R N W.a₁) (by
      rw [map_add, polynomialNodeBackwardBase_q, AlgHom.commutes]
      exact polynomialInitialOpen_unit W s b3 b4 b6 r)

/-- The reverse map retains all original unlocalized node functions. -/
theorem polynomialNodeBackward_base (z : N) :
    polynomialNodeBackward W s b3 b4 b6 r hr (algebraMap N L z) =
      polynomialNodeBackwardBase W s b3 b4 b6 r hr z := by
  rw [polynomialNodeBackward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The full reverse map retains the corrected incidence. -/
theorem polynomialNodeBackward_p :
    polynomialNodeBackward W s b3 b4 b6 r hr (algebraMap N L (NodalFiber.p s)) =
      ι (t W s b3 b4 b6) * ι U := by
  rw [polynomialNodeBackward_base, polynomialNodeBackwardBase_p]

/-- The full reverse map retains the small tangent coordinate. -/
theorem polynomialNodeBackward_q :
    polynomialNodeBackward W s b3 b4 b6 r hr (algebraMap N L (NodalFiber.q s)) = ι V := by
  rw [polynomialNodeBackward_base, polynomialNodeBackwardBase_q]

end FLT.Mazur.WeierstrassModificationX
