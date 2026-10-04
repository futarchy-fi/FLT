/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonInterpolationEquations

/-!
# Conductor generators in the genuine Möbius coordinate

The equal-endpoint ring generators are evaluated by its actual puncture map.
-/

@[expose] public noncomputable section
open scoped Polynomial
namespace FLT.Mazur.OneGonTransition
open PolygonNodePresentation
variable (K : Type*) [Field K]

/-- The conductor is t(t-1) under restriction from B. -/
lemma puncture_conductor :
    bPunctureMap (u (R := K)) = (coordinate K : puncture K) * (difference K : puncture K) := by
  change algebraMap K[X] (puncture K) (Polynomial.X * (Polynomial.X - 1)) = _
  rw [map_mul, difference_val, coordinate_val, map_sub, map_one]

/-- The first conductor monomial is t²(t-1). -/
lemma puncture_monomial :
    bPunctureMap (v (R := K)) = (coordinate K : puncture K) ^ 2 * (difference K : puncture K) := by
  change algebraMap K[X] (puncture K)
    (Polynomial.X * (Polynomial.X * (Polynomial.X - 1))) = _
  rw [map_mul, map_mul, difference_val, coordinate_val, map_sub, map_one]
  ring

/-- Multiplying the conductor by (z-1)² gives z. -/
lemma conductor_mobius :
    bPunctureMap (u (R := K)) * ((mobius K : puncture K) - 1) ^ 2 =
      (mobius K : puncture K) := by
  rw [puncture_conductor, mobius_sub_one]
  change (coordinate K : puncture K) * ↑(difference K) * (↑(difference K)⁻¹) ^ 2 =
    ↑(coordinate K) * ↑(difference K)⁻¹
  rw [pow_two, mul_assoc, ← mul_assoc (↑(difference K) : puncture K),
    Units.mul_inv, one_mul]

/-- Multiplying the first conductor monomial by (z-1)³ gives z². -/
lemma monomial_mobius :
    bPunctureMap (v (R := K)) * ((mobius K : puncture K) - 1) ^ 3 =
      (mobius K : puncture K) ^ 2 := by
  rw [puncture_monomial, mobius_sub_one]
  change (coordinate K : puncture K) ^ 2 * ↑(difference K) * (↑(difference K)⁻¹) ^ 3 =
    (↑(coordinate K) * ↑(difference K)⁻¹) ^ 2
  rw [pow_succ, mul_pow]
  calc
    _ = (coordinate K : puncture K) ^ 2 * (↑(difference K)⁻¹) ^ 2 *
      (↑(difference K) * ↑(difference K)⁻¹) := by ring
    _ = _ := by rw [Units.mul_inv, mul_one]

end FLT.Mazur.OneGonTransition
