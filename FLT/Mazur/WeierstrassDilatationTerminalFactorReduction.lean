/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalFactorEvaluation
public import FLT.Mazur.NilpotentQuadraticDifferenceReduction

/-!
# Arithmetic reductions of the terminal factors in the original cubic

The first full factor reduces to y, and the opposite factor to y+a1*x.
These identities retain the original nilpotent ideal under arbitrary evaluation.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6
variable {S : Type*} [CommRing S] [Algebra R S] (g : Coordinate W s b3 b4 b6 →ₐ[R] S)

local notation "f" => algebraMap R S
local notation "u" => g (x W s b3 b4 b6)
local notation "v" => g (y W s b3 b4 b6)

local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F I h4 h6 hrI
local notation "K" => DifferenceNode.normalCorrection H b3 I hI hH
local notation "hK" => DifferenceNode.normalCorrection_mem H b3 I hI hH
local notation "a" => DifferenceNode.criticalSlope H b3 I hI hH
local notation "P" => v - u * r.eval₂ f u - f a
local notation "Q" => v + u * (f W.a₁ + r.eval₂ f u) + f b3 + f a
local notation "J" => I.map f

/-- The complete first factor still reduces to the original ordinate. -/
theorem terminalNodeSmall_sub_y_mem :
    g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6) - v ∈ J := by
  have ht : P - v ∈ J := by
    have h := (J).sub_mem ((J).neg_mem ((J).mul_mem_left u
      (NilpotentPolynomialInverse.eval₂_mem I f r hrI u)))
        (Ideal.mem_map_of_mem f (DifferenceNode.criticalSlope_mem H b3 I hI hH))
    convert h using 1
    ring
  rw [terminalNodeSmall_evaluation]
  convert (J).add_mem (NilpotentQuadraticDifference.smallFactor_sub_mem K I hI hK f P Q)
    ht using 1
  ring

/-- The opposite factor reduces to the original opposite linear tangent. -/
theorem terminalNodeOpposite_sub_tangent_mem (h3 : b3 ∈ I) :
    g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6) -
      (v + u * f W.a₁) ∈ J := by
  have ht : Q - (v + u * f W.a₁) ∈ J := by
    have h := (J).add_mem ((J).add_mem ((J).mul_mem_left u
      (NilpotentPolynomialInverse.eval₂_mem I f r hrI u)) (Ideal.mem_map_of_mem f h3))
        (Ideal.mem_map_of_mem f (DifferenceNode.criticalSlope_mem H b3 I hI hH))
    convert h using 1
    ring
  rw [terminalNodeOpposite_evaluation]
  convert (J).add_mem (NilpotentQuadraticDifference.oppositeFactor_sub_mem K I hI hK f P Q)
    ht using 1
  ring

/-- The first full factor is a unit wherever the original ordinate is a unit. -/
theorem terminalNodeSmall_unit_of_y (hy : IsUnit v) :
    IsUnit (g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6)) :=
  NilpotentQuadraticDifference.isUnit_of_sub_mem I hI f hy
    (terminalNodeSmall_sub_y_mem W s b3 b4 b6 r I hI hrI ha h4 h6 g)

/-- The other full factor is a unit wherever the original opposite tangent is a unit. -/
theorem terminalNodeOpposite_unit_of_tangent (h3 : b3 ∈ I) (hv : IsUnit (v + u * f W.a₁)) :
    IsUnit (g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6)) :=
  NilpotentQuadraticDifference.isUnit_of_sub_mem I hI f hv
    (terminalNodeOpposite_sub_tangent_mem W s b3 b4 b6 r I hI hrI ha h4 h6 g h3)

end FLT.Mazur.WeierstrassDilatation
