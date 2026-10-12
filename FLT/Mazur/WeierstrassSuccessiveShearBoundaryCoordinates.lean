/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveXConicBoundaryCoordinates

/-!
# Original divided functions on the coefficient-split conic boundary

The actual tensor transition sends the next divided x to t⁻¹ and y to
(v+r)/t. These are identities of full coordinate algebras before choosing
a punctured branch or a rational point.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen U c
local notation "e" => tensorShearConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "q" => tensorXOpenCoefficient W s π b3 b4 b6 S
local notation "u" => conicBoundaryUnit U c
local notation "T" => WeierstrassDilatation.ScalarExtension W (s * π) b3 b4 b6 S
local notation "tx" => WeierstrassDilatation.tensorX W (s * π) b3 b4 b6 S
local notation "ty" => WeierstrassDilatation.tensorY W (s * π) b3 b4 b6 S

/-- The original integral incidence unit becomes the actual conic incidence unit. -/
theorem tensorShearConicBoundary_unit :
    e (q (↑(xOpenUnit W s π b3 b4 b6))) = (↑u : B) := by
  rw [xOpenUnit_val, tensorXOpenCoefficient_base, tensorShearConicOpenEquiv_base]
  change algebraMap C₀ B
    (tensorShearConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      (tensorCoord W s π b3 b4 b6 S 0)) = _
  rw [tensorShearConicMap_coord]
  exact (conicBoundaryUnit_val U c).symm

/-- The inverse original incidence unit is retained as well. -/
theorem tensorShearConicBoundary_inverse :
    e (q (↑(xOpenUnit W s π b3 b4 b6)⁻¹)) = (↑u⁻¹ : B) := by
  apply (u).isUnit.mul_left_inj.mp
  rw [← tensorShearConicBoundary_unit W s π b3 b4 b6 S r hs hp h3 h4 hr,
    ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one,
    tensorShearConicBoundary_unit, Units.inv_mul]

/-- Restrict the complete original next divided tensor algebra to this conic boundary. -/
def tensorShearDividedConicMap : T →ₐ[S] B :=
  (tensorShearDividedConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr).toAlgHom.comp
    (IsScalarTower.toAlgHom S T _)

/-- The actual next divided x is reciprocal to the original incidence function. -/
theorem tensorShearDividedConicMap_x :
    tensorShearDividedConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr tx = (↑u⁻¹ : B) := by
  change e (tensorOverlapEquiv W s π b3 b4 b6 S
    (algebraMap T _ ((1 : S) ⊗ₜ[R] WeierstrassDilatation.x W (s * π) b3 b4 b6))) = _
  rw [← tensorDividedOpenCoefficient_base, tensorOverlapEquiv_coefficient]
  change e (q (overlapForward W s π b3 b4 b6 _)) = _
  rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_x]
  exact tensorShearConicBoundary_inverse W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- The actual next divided y retains the unsheared slope v+r on the whole overlap. -/
theorem tensorShearDividedConicMap_y :
    tensorShearDividedConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr ty =
      (↑u⁻¹ : B) * (algebraMap C₀ B (conicV a c) + algebraMap S B r) := by
  change e (tensorOverlapEquiv W s π b3 b4 b6 S
    (algebraMap T _ ((1 : S) ⊗ₜ[R] WeierstrassDilatation.y W (s * π) b3 b4 b6))) = _
  rw [← tensorDividedOpenCoefficient_base, tensorOverlapEquiv_coefficient]
  change e (q (overlapForward W s π b3 b4 b6 _)) = _
  rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_y, map_mul, map_mul,
    tensorShearConicBoundary_inverse]
  congr 1
  change e (q (algebraMap (Coordinate W s π b3 b4 b6) _
    (coord W s π b3 b4 b6 1))) = _
  rw [tensorXOpenCoefficient_base, tensorShearConicOpenEquiv_base]
  change algebraMap C₀ B
    (tensorShearConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      (tensorCoord W s π b3 b4 b6 S 1)) = _
  rw [tensorShearConicMap_coord]
  change algebraMap C₀ B (conicV a c + algebraMap S C₀ r) = _
  rw [map_add, ← IsScalarTower.algebraMap_apply S C₀ B]

end FLT.Mazur.WeierstrassSuccessiveX
