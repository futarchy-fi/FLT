/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShear

public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Vertical derivatives under the divided shear

The forward and inverse substitutions preserve the actual vertical derivative.
This lets smoothness certificates return to the original curve.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
attribute [local irreducible] rootShearCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r

/-- Returning the output preserves its full vertical derivative. -/
@[simp] theorem shearForward_verticalDerivative :
    shearForward W s b3 b4 b6 r (verticalDerivative W s b3 b4 b6) =
      verticalDerivative U s b3 (b4 - r * b3) b6 := by
  simp only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    shearForward_x, shearForward_y, (rootShearCurve_coefficients r).1]
  ring

/-- The inverse substitution also preserves the full vertical derivative. -/
@[simp] theorem shearBackward_verticalDerivative :
    shearBackward W s b3 b4 b6 r (verticalDerivative U s b3 (b4 - r * b3) b6) =
      verticalDerivative W s b3 b4 b6 := by
  simp only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    shearBackward_x, shearBackward_y, (rootShearCurve_coefficients r).1]
  ring

end FLT.Mazur.WeierstrassDilatation
