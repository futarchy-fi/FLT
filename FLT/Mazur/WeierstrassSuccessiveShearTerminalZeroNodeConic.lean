/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalZeroConicCoordinates
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalNodeConic
public import FLT.Mazur.WeierstrassDilatationShearNodeNormalForm
public import FLT.Mazur.NodalFiberNodeComparison

/-!
# Ordered terminal node coordinates on the full scale-one sheared conic boundary

Normalize the entire original tensor equation and keep both tangent factors.
The root shift cancels only after restricting the actual original functions.
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
  (hs : algebraMap R S (π ^ k) = 1) (hp : algebraMap R S π = 0)
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
variable (h6 : algebraMap R S b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (k + 1)) = 0 from by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "E" => tensorShearTerminalNodeEquiv W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
local notation "φ" => tensorShearScaleOneTerminalConicMap W π k b3 b4 b6 S r hs hp h3 h4 hr
local notation "v" => conicBoundaryUnit U c
local notation "tx" => (1 : S) ⊗ₜ[R] x
local notation "ty" => (1 : S) ⊗ₜ[R] y

/-- The full terminal node restricts along the actual integral conic transition. -/
def tensorShearScaleOneTerminalNodeConicMap : PolygonNodeEqualizer.A (R := S) →ₐ[S] B :=
  (φ).comp (E).symm.toAlgHom

local notation "ψ" => tensorShearScaleOneTerminalNodeConicMap W π k b3 b4 b6 S r
  hs hp h3 h4 hr h6 a ha

/-- The first ordered tangent factor restricts to the unshifted slope divided by incidence. -/
theorem tensorShearScaleOneTerminalNodeConicMap_first : ψ PolygonNodeLocalization.x =
    (↑v⁻¹ : B) * algebraMap C₀ B (conicV (U).a₁ c) := by
  have H : E (ty - algebraMap S D r * tx) = PolygonNodeLocalization.x := by
    rw [map_sub, map_mul, AlgEquiv.commutes,
      tensorShearTerminalNode_y, tensorShearTerminalNode_x]
    ring
  rw [← H]
  change φ ((E).symm ((E) (ty - algebraMap S D r * tx))) = _
  rw [AlgEquiv.symm_apply_apply, map_sub, map_mul, AlgHom.commutes,
    tensorShearScaleOneTerminalConicMap_x W π k b3 b4 b6 S r hs hp h3 h4 hr,
    tensorShearScaleOneTerminalConicMap_y W π k b3 b4 b6 S r hs hp h3 h4 hr]
  ring

/-- The second tangent factor retains the opposite original tangent orientation. -/
theorem tensorShearScaleOneTerminalNodeConicMap_second : ψ PolygonNodeLocalization.y =
    (↑v⁻¹ : B) * (algebraMap C₀ B (conicV (U).a₁ c) + algebraMap S B (U).a₁) := by
  have H : E (ty + algebraMap S D ((a : S) - r) * tx) =
      PolygonNodeLocalization.y := by
    rw [map_add, map_mul, AlgEquiv.commutes, map_sub,
      tensorShearTerminalNode_y, tensorShearTerminalNode_x]
    have hi : algebraMap S (PolygonNodeEqualizer.A (R := S)) (a : S) *
        algebraMap S _ (↑a⁻¹ : S) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (PolygonNodeLocalization.y - PolygonNodeLocalization.x) * hi
  rw [← H]
  change φ ((E).symm ((E) (ty + algebraMap S D ((a : S) - r) * tx))) = _
  rw [AlgEquiv.symm_apply_apply, map_add, map_mul, AlgHom.commutes,
    tensorShearScaleOneTerminalConicMap_x W π k b3 b4 b6 S r hs hp h3 h4 hr,
    tensorShearScaleOneTerminalConicMap_y W π k b3 b4 b6 S r hs hp h3 h4 hr, map_sub, ha]
  ring

end FLT.Mazur.WeierstrassSuccessiveX
