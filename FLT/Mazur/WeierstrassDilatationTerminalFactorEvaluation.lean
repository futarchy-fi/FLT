/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalRestriction

/-!
# Terminal node coordinates evaluated in the original abscissa and ordinate

The formulas retain the entire original polynomial tangent root, critical
translation and quadratic correction under every coefficient-preserving map.
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

/-- The original horizontal polynomial is evaluated at the actual image of x. -/
theorem terminalPolynomial_map : g (algebraMap R[X] A r) = r.eval₂ f u := by
  have he : r.eval₂ (algebraMap R A) (x W s b3 b4 b6) = algebraMap R[X] A r :=
    Polynomial.eval₂_algebraMap_X r (Algebra.algHom R R[X] A)
  rw [← he, Polynomial.algHom_eval₂_algebraMap]

/-- The first unnormalized tangent retains the original x and y images. -/
theorem terminalSmallTangent_map :
    g (terminalSmallTangent W s b3 b4 b6 r) = v - u * r.eval₂ f u := by
  simp only [terminalSmallTangent, map_sub, map_mul, terminalPolynomial_map]

/-- The opposite unnormalized tangent also retains b3 and the original a1. -/
theorem terminalOppositeTangent_map :
    g (terminalOppositeTangent W s b3 b4 b6 r) =
      v + u * (f W.a₁ + r.eval₂ f u) + f b3 := by
  simp only [terminalOppositeTangent, map_add, map_mul, AlgHom.commutes, terminalPolynomial_map]

local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F I h4 h6 hrI
local notation "K" => DifferenceNode.normalCorrection H b3 I hI hH
local notation "hK" => DifferenceNode.normalCorrection_mem H b3 I hI hH
local notation "a" => DifferenceNode.criticalSlope H b3 I hI hH
local notation "P" => v - u * r.eval₂ f u - f a
local notation "Q" => v + u * (f W.a₁ + r.eval₂ f u) + f b3 + f a

/-- The full first node factor in terms of the original x and y images. -/
theorem terminalNodeSmall_evaluation :
    g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6) =
      NilpotentQuadraticDifference.smallFactor K I hI hK f P Q := by
  rw [terminalNodeSmall_map, terminalSmallTangent_map, terminalOppositeTangent_map]

/-- The full opposite node factor in terms of the original x and y images. -/
theorem terminalNodeOpposite_evaluation :
    g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6) =
      NilpotentQuadraticDifference.oppositeFactor K I hI hK f P Q := by
  rw [terminalNodeOpposite_map, terminalSmallTangent_map, terminalOppositeTangent_map]

end FLT.Mazur.WeierstrassDilatation
