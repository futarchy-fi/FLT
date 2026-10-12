/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientShear
public import FLT.Mazur.WeierstrassDilatationResidueGeometry
public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.NodalFiberBoundedParameterTransport

/-!
# Laurent normalization of the arbitrary-root nonsingular terminal equation

The divided constant remains invertible. The full equation has Laurent
parameter equal to the sheared ordinate, with the original root shift retained.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
open LaurentPolynomial
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Type*} [CommRing S] (U : WeierstrassCurve S) (a : Sˣ)
  (s b3 b4 b6 : S) (hs : s = 0) (h3 : b3 = 0) (h4 : b4 = 0)
  (ha : U.a₁ = a) (h2 : U.a₂ = 0)

/-- The whole divided equation becomes the product tangent equation. -/
def zeroLinearProductEquiv : Coordinate U s b3 b4 b6 ≃ₐ[S] NodalFiber.Coordinate b6 := by
  subst s b3 b4
  exact fiberTangentEquiv U a b6 ha h2

/-- The divided abscissa is the difference of the two tangent factors. -/
theorem zeroLinearProductEquiv_x :
    zeroLinearProductEquiv U a s b3 b4 b6 hs h3 h4 ha h2 (x U s b3 b4 b6) =
      algebraMap S _ (↑a⁻¹ : S) * (NodalFiber.q b6 - NodalFiber.p b6) := by
  subst s b3 b4
  exact fiberToTangent_x U a b6 ha h2

/-- The divided ordinate is the first tangent factor. -/
theorem zeroLinearProductEquiv_y :
    zeroLinearProductEquiv U a s b3 b4 b6 hs h3 h4 ha h2 (y U s b3 b4 b6) =
      NodalFiber.p b6 := by
  subst s b3 b4
  exact fiberToTangent_y U a b6 ha h2

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S] (r : S)
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
variable (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : IsUnit (algebraMap R S b6))

/-- The complete nonsingular sheared equation has its actual Laurent coordinate. -/
def coefficientShearLaurentEquiv :
    Coordinate U (q s) (q b3) (q b4 - r * q b3) (q b6) ≃ₐ[S] S[T;T⁻¹] :=
  (zeroLinearProductEquiv U a (q s) (q b3) (q b4 - r * q b3) (q b6) hs h3
    (by rw [h3, h4, mul_zero, sub_zero]) ha.symm
    (WeierstrassModificationX.coefficientShear_a₂_zero W S r hr)).trans
      (NodalFiber.unitLaurentBoundedCast hc.unit (q b6) hc.unit_spec)

/-- The whole sheared coefficient abscissa retains its actual tangent normalization. -/
theorem coefficientShearLaurentEquiv_x :
    coefficientShearLaurentEquiv W s b3 b4 b6 S r hs h3 h4 hr a ha hc
      (x U (q s) (q b3) (q b4 - r * q b3) (q b6)) =
      C (↑a⁻¹ : S) * (C (q b6) * T (-1) - T 1) := by
  rw [coefficientShearLaurentEquiv, AlgEquiv.trans_apply, zeroLinearProductEquiv_x,
    map_mul, map_sub, AlgEquiv.commutes, NodalFiber.unitLaurentBoundedCast_q,
    NodalFiber.unitLaurentBoundedCast_p]
  rfl

/-- The whole sheared coefficient ordinate is the first normalized tangent factor. -/
theorem coefficientShearLaurentEquiv_y :
    coefficientShearLaurentEquiv W s b3 b4 b6 S r hs h3 h4 hr a ha hc
      (y U (q s) (q b3) (q b4 - r * q b3) (q b6)) = T 1 := by
  rw [coefficientShearLaurentEquiv, AlgEquiv.trans_apply, zeroLinearProductEquiv_y,
    NodalFiber.unitLaurentBoundedCast_p]

/-- The original tensor equation retains the same complete Laurent normal form. -/
def tensorShearLaurentEquiv : ScalarExtension W s b3 b4 b6 S ≃ₐ[S]
    S[T;T⁻¹] :=
  (dividedCoefficientShearEquiv W s b3 b4 b6 S r).trans
    (coefficientShearLaurentEquiv W s b3 b4 b6 S r hs h3 h4 hr a ha hc)

/-- The original tensor abscissa keeps the full difference of tangent factors. -/
theorem tensorShearLaurentEquiv_x :
    tensorShearLaurentEquiv W s b3 b4 b6 S r hs h3 h4 hr a ha hc
      ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) =
      C (↑a⁻¹ : S) * (C (q b6) * T (-1) - T 1) := by
  change coefficientShearLaurentEquiv W s b3 b4 b6 S r hs h3 h4 hr a ha hc
    (dividedCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [dividedCoefficientShearEquiv_tmul, one_smul, coefficientMap_x,
    shearForward_x, coefficientShearLaurentEquiv_x]

/-- The original tensor ordinate retains its actual root shift on the complete Laurent chart. -/
theorem tensorShearLaurentEquiv_y :
    tensorShearLaurentEquiv W s b3 b4 b6 S r hs h3 h4 hr a ha hc
      ((1 : S) ⊗ₜ[R] y W s b3 b4 b6) =
      T 1 + C r *
        (C (↑a⁻¹ : S) * (C (q b6) * T (-1) - T 1)) := by
  change coefficientShearLaurentEquiv W s b3 b4 b6 S r hs h3 h4 hr a ha hc
    (dividedCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [dividedCoefficientShearEquiv_tmul, one_smul, coefficientMap_y, shearForward_y,
    map_add, map_mul, AlgEquiv.commutes,
    coefficientShearLaurentEquiv_x, coefficientShearLaurentEquiv_y]
  rfl

end FLT.Mazur.WeierstrassDilatation
