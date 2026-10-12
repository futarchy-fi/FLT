/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveXDepthTensorOverlap
public import FLT.Mazur.WeierstrassSuccessiveXConicBoundaryCoordinates

/-!
# Original terminal divided coordinates on the arbitrary-root conic boundary

The actual integral depth transition retains reciprocal incidence and the
root-shifted slope on every coefficient fiber.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S b6
local notation "C₀" => ConicCoordinate (U).a₁ c
local notation "B" => MiddleConicOpen U c
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 S
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "E" => tensorShearConicOpenEquiv W (π ^ k) π b3 b4 b6 S r hs hp h3 h4 hr
local notation "A" => PrincipalOpenTensor.transition S x t (depthOverlapEquiv W π k b3 b4 b6)
local notation "f" => PrincipalOpenTensor.coefficient S t
local notation "v" => conicBoundaryUnit U c
local notation "w" => xOpenUnit W (π ^ k) π b3 b4 b6

/-- The original integral incidence unit becomes the full sheared conic incidence unit. -/
theorem tensorShearTerminalConic_unit : E (f (↑w)) = (↑v : B) := by
  rw [xOpenUnit_val, PrincipalOpenTensor.coefficient_base]
  change E (algebraMap T₀ _ (tensorCoord W (π ^ k) π b3 b4 b6 S 0)) = _
  rw [tensorShearConicOpenEquiv_base, tensorShearConicMap_coord, conicBoundaryUnit_val]
  rfl

/-- The inverse incidence also survives the actual integral tensor transition. -/
theorem tensorShearTerminalConic_inverse : E (f (↑w⁻¹)) = (↑v⁻¹ : B) := by
  apply (IsUnit.mul_left_inj (Units.isUnit v)).mp
  rw [← tensorShearTerminalConic_unit W π k b3 b4 b6 S r hs hp h3 h4 hr,
    ← map_mul]
  erw [← map_mul, Units.inv_mul, map_one, map_one,
    tensorShearTerminalConic_unit, Units.inv_mul]

/-- Restriction of the complete original divided tensor equation along its actual boundary. -/
def tensorShearTerminalConicMap : D →ₐ[S] B :=
  (E).toAlgHom.comp ((A).toAlgHom.comp (IsScalarTower.toAlgHom S D _))

/-- The original terminal abscissa is the reciprocal conic incidence. -/
theorem tensorShearTerminalConicMap_x :
    tensorShearTerminalConicMap W π k b3 b4 b6 S r hs hp h3 h4 hr
      ((1 : S) ⊗ₜ[R] x) = (↑v⁻¹ : B) := by
  change E (A (algebraMap D _ ((1 : S) ⊗ₜ[R] x))) = _
  rw [← PrincipalOpenTensor.coefficient_base S x x,
    PrincipalOpenTensor.transition_coefficient, depthOverlapEquiv_x]
  exact tensorShearTerminalConic_inverse W π k b3 b4 b6 S r hs hp h3 h4 hr

/-- The original terminal ordinate retains the arbitrary tangent root in its slope. -/
theorem tensorShearTerminalConicMap_y :
    tensorShearTerminalConicMap W π k b3 b4 b6 S r hs hp h3 h4 hr
      ((1 : S) ⊗ₜ[R] y) =
        (↑v⁻¹ : B) * (algebraMap C₀ B (conicV (U).a₁ c) + algebraMap S B r) := by
  change E (A (algebraMap D _ ((1 : S) ⊗ₜ[R] y))) = _
  rw [← PrincipalOpenTensor.coefficient_base S x y,
    PrincipalOpenTensor.transition_coefficient, depthOverlapEquiv_y, map_mul, map_mul,
    tensorShearTerminalConic_inverse, PrincipalOpenTensor.coefficient_base]
  change _ * E (algebraMap T₀ _ (tensorCoord W (π ^ k) π b3 b4 b6 S 1)) = _
  rw [tensorShearConicOpenEquiv_base, tensorShearConicMap_coord]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_add,
    ← IsScalarTower.algebraMap_apply S C₀ B]

end FLT.Mazur.WeierstrassSuccessiveX
