/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentShear
public import FLT.Mazur.NodeTangentTensorOrientation
public import FLT.Mazur.WeierstrassIntegralChart

/-!
# The root-sheared normalization chart of the original nodal equation

Over the actual tangent algebra, x=z(z+a) and y=(z+s)x solve the
original nodal equation, where s is the adjoined root and a=a₁+2s.
The map keeps the original unsheared coordinates and both tangent factors.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur
open Polynomial WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "s" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)

/-- The original x coordinate on the root-sheared affine normalization chart. -/
def nodeTangentNormalizationX : S[X] := X * (X + C a)

/-- The original, unsheared y coordinate on that same chart. -/
def nodeTangentNormalizationY : S[X] := (X + C s) * nodeTangentNormalizationX W

/-- The normalization coordinates satisfy the original nodal cubic, including its a₂ term. -/
theorem nodeTangentNormalization_equation
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    (W.map (algebraMap R S[X])).toProjective.Equation
      ![nodeTangentNormalizationX W, nodeTangentNormalizationY W, 1] := by
  have hr := congrArg (C : S →+* S[X]) (nodeTangentRoot_equation W)
  simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hr
  rw [WeierstrassCurve.Projective.equation_iff]
  change nodeTangentNormalizationY W ^ 2 * 1 +
      algebraMap R S[X] W.a₁ * nodeTangentNormalizationX W *
        nodeTangentNormalizationY W * 1 +
      algebraMap R S[X] W.a₃ * nodeTangentNormalizationY W * 1 ^ 2 -
      (nodeTangentNormalizationX W ^ 3 +
        algebraMap R S[X] W.a₂ * nodeTangentNormalizationX W ^ 2 * 1 +
        algebraMap R S[X] W.a₄ * nodeTangentNormalizationX W * 1 ^ 2 +
        algebraMap R S[X] W.a₆ * 1 ^ 3) = 0
  simp only [h₃, h₄, h₆, map_zero, zero_mul, add_zero, mul_one]
  simp only [nodeTangentNormalizationY, nodeTangentNormalizationX,
    (nodeTangentShear_coefficients W).1, map_add, map_mul, map_ofNat]
  linear_combination (X * (X + (C (algebraMap R S W.a₁) + 2 * C s))) ^ 2 * hr

/-- Evaluation from the original affine chart, with no split-equation substitution. -/
def nodeTangentNormalizationChart
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    Coordinate W 2 →ₐ[R] S[X] :=
  evaluation W 2 ![nodeTangentNormalizationX W, nodeTangentNormalizationY W, 1]
    (nodeTangentNormalization_equation W h₃ h₄ h₆) rfl

@[simp] theorem nodeTangentNormalizationChart_coord
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) (i : Fin 3) :
    nodeTangentNormalizationChart W h₃ h₄ h₆ (coord W 2 i) =
      ![nodeTangentNormalizationX W, nodeTangentNormalizationY W, 1] i :=
  evaluation_coord _ _ _ _ _ i

/-- Extend the original affine chart evaluation over the actual root coefficient tensor product. -/
def nodeTangentNormalizationTensor
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    S ⊗[R] Coordinate W 2 →ₐ[R] S[X] :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S S[X])
    (nodeTangentNormalizationChart W h₃ h₄ h₆) (fun _ _ => Commute.all _ _)

@[simp] theorem nodeTangentNormalizationTensor_tmul
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
    (c : S) (b : Coordinate W 2) :
    nodeTangentNormalizationTensor W h₃ h₄ h₆ (c ⊗ₜ[R] b) =
      C c * nodeTangentNormalizationChart W h₃ h₄ h₆ b := rfl

/-- The first original tangent factor is z times the original x coordinate. -/
theorem nodeTangentNormalizationTensor_first
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    nodeTangentNormalizationTensor W h₃ h₄ h₆
        (nodeTangentTensorFirst W (coord W 2 0) (coord W 2 1)) =
      X * nodeTangentNormalizationX W := by
  simp only [nodeTangentTensorFirst, map_sub, nodeTangentNormalizationTensor_tmul,
    map_one, one_mul, nodeTangentNormalizationChart_coord,
    Matrix.cons_val_zero, Matrix.cons_val_one, nodeTangentNormalizationY]
  ring

/-- The companion original factor is (z+a) times that same x coordinate. -/
theorem nodeTangentNormalizationTensor_second
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    nodeTangentNormalizationTensor W h₃ h₄ h₆
        (nodeTangentTensorSecond W (coord W 2 0) (coord W 2 1)) =
      (X + C a) * nodeTangentNormalizationX W := by
  simp only [nodeTangentTensorSecond, map_add, nodeTangentNormalizationTensor_tmul,
    map_one, one_mul, nodeTangentNormalizationChart_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one, nodeTangentNormalizationY, (nodeTangentShear_coefficients W).1,
    map_mul, map_ofNat]
  ring

end FLT.Mazur
