/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalNodeConic
public import FLT.Mazur.WeierstrassDilatationShearNodeNormalForm
public import FLT.Mazur.NodalFiberNodeComparison

/-!
# Original functions on both complete terminal branches

Restrict the sealed tensor node equivalence to its two polynomial branches.
The original coordinates keep their tangent scale and root shift at the origin.
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
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
variable (h6 : algebraMap R S b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "E" => tensorShearTerminalNodeEquiv W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
open Polynomial

/-- Restriction of the entire original tensor equation to the first node branch. -/
def tensorShearTerminalFirstMap : D →ₐ[S] S[X] :=
  PolygonNodeEqualizer.first.comp (E).toAlgHom

/-- The original abscissa on the complete first branch, including its origin. -/
theorem tensorShearTerminalFirstMap_x :
    tensorShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
      ((1 : S) ⊗ₜ[R] x) = -C (↑a⁻¹ : S) * X := by
  change PolygonNodeEqualizer.first (E ((1 : S) ⊗ₜ[R] x)) = _
  rw [tensorShearTerminalNode_x, map_mul, map_sub, AlgHom.commutes,
    PolygonNodeLocalization.first_y, PolygonNodeLocalization.first_x]
  simp only [Polynomial.algebraMap_eq, zero_sub, mul_neg, neg_mul]

/-- The original ordinate retains its root shift on the entire first branch. -/
theorem tensorShearTerminalFirstMap_y :
    tensorShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
      ((1 : S) ⊗ₜ[R] y) = X + C r * (-C (↑a⁻¹ : S) * X) := by
  change PolygonNodeEqualizer.first (E ((1 : S) ⊗ₜ[R] y)) = _
  rw [tensorShearTerminalNode_y, map_add, map_mul, map_mul, map_sub,
    AlgHom.commutes, AlgHom.commutes,
    PolygonNodeLocalization.first_y, PolygonNodeLocalization.first_x]
  simp only [Polynomial.algebraMap_eq,
    zero_sub, mul_neg, neg_mul]

/-- Restriction of the original integral equation to the first terminal branch. -/
def originalShearTerminalFirstMap :
    WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6 →ₐ[R] S[X] :=
  ((tensorShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha).restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The original integral abscissa retains the full first branch coordinate. -/
theorem originalShearTerminalFirstMap_x :
    originalShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha x =
      -C (↑a⁻¹ : S) * X := tensorShearTerminalFirstMap_x W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha

/-- The original integral ordinate retains the full first branch coordinate. -/
theorem originalShearTerminalFirstMap_y :
    originalShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha y =
      X + C r * (-C (↑a⁻¹ : S) * X) :=
  tensorShearTerminalFirstMap_y W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha

/-- Restriction of the entire original tensor equation to the second node branch. -/
def tensorShearTerminalSecondMap : D →ₐ[S] S[X] :=
  PolygonNodeEqualizer.second.comp (E).toAlgHom

/-- The original abscissa on the complete second branch, including its origin. -/
theorem tensorShearTerminalSecondMap_x :
    tensorShearTerminalSecondMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
      ((1 : S) ⊗ₜ[R] x) = C (↑a⁻¹ : S) * X := by
  change PolygonNodeEqualizer.second (E ((1 : S) ⊗ₜ[R] x)) = _
  rw [tensorShearTerminalNode_x, map_mul, map_sub, AlgHom.commutes,
    PolygonNodeLocalization.second_y, PolygonNodeLocalization.second_x]
  simp only [Polynomial.algebraMap_eq, sub_zero]

/-- The original ordinate retains its root shift on the entire second branch. -/
theorem tensorShearTerminalSecondMap_y :
    tensorShearTerminalSecondMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
      ((1 : S) ⊗ₜ[R] y) = C r * (C (↑a⁻¹ : S) * X) := by
  change PolygonNodeEqualizer.second (E ((1 : S) ⊗ₜ[R] y)) = _
  rw [tensorShearTerminalNode_y, map_add, map_mul, map_mul, map_sub,
    AlgHom.commutes, AlgHom.commutes,
    PolygonNodeLocalization.second_y, PolygonNodeLocalization.second_x]
  simp only [Polynomial.algebraMap_eq,
    sub_zero, zero_add]

/-- Restriction of the original integral equation to the second terminal branch. -/
def originalShearTerminalSecondMap :
    WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6 →ₐ[R] S[X] :=
  ((tensorShearTerminalSecondMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha).restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The original integral abscissa retains the full second branch coordinate. -/
theorem originalShearTerminalSecondMap_x :
    originalShearTerminalSecondMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha x =
      C (↑a⁻¹ : S) * X := tensorShearTerminalSecondMap_x W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha

/-- The original integral ordinate retains the full second branch coordinate. -/
theorem originalShearTerminalSecondMap_y :
    originalShearTerminalSecondMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha y =
      C r * (C (↑a⁻¹ : S) * X) :=
  tensorShearTerminalSecondMap_y W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha

end FLT.Mazur.WeierstrassSuccessiveX
