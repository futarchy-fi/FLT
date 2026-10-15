/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra
public import FLT.Mazur.NilpotentPolynomialInverseBaseChange
public import FLT.Mazur.NilpotentQuadraticRoot

/-!
# Polynomial tangent factors of the full terminal arithmetic equation

A polynomial small root absorbs the cubic and quadratic horizontal terms.
The remaining product retains the original constant and its linear correction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)

include hs h2 in
/-- The full terminal quadratic correction lies in the extended arithmetic ideal. -/
theorem terminalTangentConstant_mem : C W.a₂ + C s * X ∈ I.map C :=
  (I.map C).add_mem (Ideal.mem_map_of_mem C h2)
    ((I.map C).mul_mem_right X (Ideal.mem_map_of_mem C hs))

/-- The original cubic coefficient constructs a root on the entire horizontal line. -/
def terminalTangentRoot : R[X] :=
  NilpotentQuadraticRoot.root (I.map C) (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI C)
    (C W.a₁) (C W.a₂ + C s * X) (ha.map C) (terminalTangentConstant_mem W s I hs h2)

/-- The polynomial tangent root retains the original cubic term at every horizontal value. -/
theorem terminalTangentRoot_equation :
    terminalTangentRoot W s I hI ha hs h2 ^ 2 + C W.a₁ *
      terminalTangentRoot W s I hI ha hs h2 = C W.a₂ + C s * X :=
  NilpotentQuadraticRoot.root_equation ..

/-- The full terminal tangent root retains the small arithmetic label. -/
theorem terminalTangentRoot_mem : terminalTangentRoot W s I hI ha hs h2 ∈ I.map C :=
  NilpotentQuadraticRoot.root_mem ..

variable (b3 b4 b6 : R) (r : R[X])
local notation "A" => Coordinate W s b3 b4 b6
local notation "f" => algebraMap R[X] A

/-- The full terminal small tangent coordinate, including the origin. -/
def terminalSmallTangent : A := y W s b3 b4 b6 - x W s b3 b4 b6 * f r

/-- The full terminal opposite coordinate retains the original linear vertical coefficient. -/
def terminalOppositeTangent : A :=
  y W s b3 b4 b6 + x W s b3 b4 b6 * (algebraMap R A W.a₁ + f r) + algebraMap R A b3

variable (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)

include hr in
/-- The full original terminal equation factors with its remaining linear correction intact. -/
theorem terminalTangents_product :
    terminalSmallTangent W s b3 b4 b6 r * terminalOppositeTangent W s b3 b4 b6 r =
      algebraMap R A b6 + (algebraMap R A b4 - algebraMap R A b3 * f r) * x W s b3 b4 b6 := by
  have hh := congrArg f hr
  have hc (z : R) : f (C z) = algebraMap R A z :=
    (IsScalarTower.algebraMap_apply R R[X] A z).symm
  simp only [map_add, map_mul, map_pow, hc] at hh
  change f r ^ 2 + algebraMap R A W.a₁ * f r =
    algebraMap R A W.a₂ + algebraMap R A s * x W s b3 b4 b6 at hh
  simp only [terminalSmallTangent, terminalOppositeTangent]
  linear_combination equation W s b3 b4 b6 - x W s b3 b4 b6 ^ 2 * hh

/-- The corrected terminal tangent difference is an invertible-linear polynomial in x. -/
theorem terminalTangents_difference :
    terminalOppositeTangent W s b3 b4 b6 r - terminalSmallTangent W s b3 b4 b6 r -
      algebraMap R A b3 = x W s b3 b4 b6 * (algebraMap R A W.a₁ + f r + f r) := by
  simp only [terminalSmallTangent, terminalOppositeTangent]
  ring

end FLT.Mazur.WeierstrassDilatation
