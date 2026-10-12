/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientShear
public import FLT.Mazur.WeierstrassDilatationResidueGeometry
public import FLT.Mazur.WeierstrassIncidenceShearNormalForm

/-!
# The full terminal node equation after a coefficient tangent shear

When the terminal coefficients vanish, the actual sheared divided equation is
the product-zero node. Its tangent factors retain the original root shift.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Type*} [CommRing S] (U : WeierstrassCurve S) (a : Sˣ)
  (s b3 b4 b6 : S) (hs : s = 0) (h3 : b3 = 0) (h4 : b4 = 0) (h6 : b6 = 0)
  (ha : U.a₁ = a) (h2 : U.a₂ = 0)

/-- The whole divided equation becomes the product-zero tangent equation. -/
def zeroLinearNodeEquiv : Coordinate U s b3 b4 b6 ≃ₐ[S] NodalFiber.Coordinate (0 : S) := by
  subst s b3 b4 b6
  exact fiberTangentEquiv U a 0 ha h2

/-- The divided abscissa is the difference of the two tangent factors. -/
theorem zeroLinearNodeEquiv_x :
    zeroLinearNodeEquiv U a s b3 b4 b6 hs h3 h4 h6 ha h2 (x U s b3 b4 b6) =
      algebraMap S _ (↑a⁻¹ : S) * (NodalFiber.q 0 - NodalFiber.p 0) := by
  subst s b3 b4 b6
  exact fiberToTangent_x U a 0 ha h2

/-- The divided ordinate is the first tangent factor. -/
theorem zeroLinearNodeEquiv_y :
    zeroLinearNodeEquiv U a s b3 b4 b6 hs h3 h4 h6 ha h2 (y U s b3 b4 b6) =
      NodalFiber.p 0 := by
  subst s b3 b4 b6
  exact fiberToTangent_y U a 0 ha h2

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S] (r : S)
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
variable (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0) (h6 : algebraMap R S b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)

/-- The actual sheared terminal coefficient equation is the full tangent node algebra. -/
def coefficientShearNodeEquiv :
    Coordinate U (q s) (q b3) (q b4 - r * q b3) (q b6) ≃ₐ[S]
      NodalFiber.Coordinate (0 : S) :=
  zeroLinearNodeEquiv U a (q s) (q b3) (q b4 - r * q b3) (q b6) hs h3
    (by rw [h3, h4, mul_zero, sub_zero]) h6 ha.symm
    (WeierstrassModificationX.coefficientShear_a₂_zero W S r hr)

/-- The whole sheared coefficient abscissa retains its actual tangent normalization. -/
theorem coefficientShearNodeEquiv_x :
    coefficientShearNodeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha
      (x U (q s) (q b3) (q b4 - r * q b3) (q b6)) =
      algebraMap S _ (↑a⁻¹ : S) * (NodalFiber.q 0 - NodalFiber.p 0) :=
  zeroLinearNodeEquiv_x U a _ _ _ _ _ _ _ _ _ _

/-- The whole sheared coefficient ordinate is the first normalized tangent factor. -/
theorem coefficientShearNodeEquiv_y :
    coefficientShearNodeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha
      (y U (q s) (q b3) (q b4 - r * q b3) (q b6)) = NodalFiber.p 0 :=
  zeroLinearNodeEquiv_y U a _ _ _ _ _ _ _ _ _ _

/-- The original tensor equation retains the same entire terminal node normal form. -/
def tensorShearNodeEquiv : ScalarExtension W s b3 b4 b6 S ≃ₐ[S]
    NodalFiber.Coordinate (0 : S) :=
  (dividedCoefficientShearEquiv W s b3 b4 b6 S r).trans
    (coefficientShearNodeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha)

/-- The original tensor abscissa keeps the full difference of tangent factors. -/
theorem tensorShearNodeEquiv_x :
    tensorShearNodeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha
      ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) =
      algebraMap S _ (↑a⁻¹ : S) * (NodalFiber.q 0 - NodalFiber.p 0) := by
  change coefficientShearNodeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha
    (dividedCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [dividedCoefficientShearEquiv_tmul, one_smul, coefficientMap_x,
    shearForward_x, coefficientShearNodeEquiv_x]

/-- The original tensor ordinate retains its actual root shift on both branches and the node. -/
theorem tensorShearNodeEquiv_y :
    tensorShearNodeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha
      ((1 : S) ⊗ₜ[R] y W s b3 b4 b6) =
      NodalFiber.p 0 + algebraMap S _ r *
        (algebraMap S _ (↑a⁻¹ : S) * (NodalFiber.q 0 - NodalFiber.p 0)) := by
  change coefficientShearNodeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha
    (dividedCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [dividedCoefficientShearEquiv_tmul, one_smul, coefficientMap_y, shearForward_y,
    map_add, map_mul, AlgEquiv.commutes,
    coefficientShearNodeEquiv_x, coefficientShearNodeEquiv_y]

end FLT.Mazur.WeierstrassDilatation
