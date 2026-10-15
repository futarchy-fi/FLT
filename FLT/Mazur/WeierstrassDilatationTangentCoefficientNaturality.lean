/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalFactorEvaluation
public import FLT.Mazur.WeierstrassDilatationCoefficients

/-!
# The original terminal tangents commute with coefficient extension

The full horizontal polynomial and both tangent coordinates are preserved,
including the original linear vertical coefficient.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
local notation "f" => algebraMap R S
local notation "U" => W.map f
local notation "A" => ExtendedCoordinate W s b3 b4 b6 S
local notation "g" => coefficientMap W s b3 b4 b6 S

/-- The complete horizontal polynomial retains its image in the extended cubic. -/
theorem terminalPolynomial_coefficients :
    g (algebraMap R[X] (Coordinate W s b3 b4 b6) r) =
      algebraMap S[X] A (r.map f) := by
  rw [terminalPolynomial_map, coefficientMap_x]
  have he : (r.map f).eval₂ (algebraMap S A)
      (x U (f s) (f b3) (f b4) (f b6)) = algebraMap S[X] A (r.map f) :=
    Polynomial.eval₂_algebraMap_X (r.map f) (Algebra.algHom S S[X] A)
  rw [← he]
  rw [Polynomial.eval₂_map, IsScalarTower.algebraMap_eq R S A]

/-- The small tangent is the tangent constructed from all the extended coefficients. -/
theorem terminalSmallTangent_coefficients :
    g (terminalSmallTangent W s b3 b4 b6 r) =
      terminalSmallTangent U (f s) (f b3) (f b4) (f b6) (r.map f) := by
  simp only [terminalSmallTangent, map_sub, map_mul, coefficientMap_x, coefficientMap_y,
    terminalPolynomial_coefficients]

/-- The opposite tangent preserves both the original a1 and the original b3. -/
theorem terminalOppositeTangent_coefficients :
    g (terminalOppositeTangent W s b3 b4 b6 r) =
      terminalOppositeTangent U (f s) (f b3) (f b4) (f b6) (r.map f) := by
  simp only [terminalOppositeTangent, map_add, map_mul, coefficientMap_x, coefficientMap_y,
    terminalPolynomial_coefficients, AlgHom.commutes, WeierstrassCurve.map_a₁,
    ← IsScalarTower.algebraMap_apply R S A]

end FLT.Mazur.WeierstrassDilatation
