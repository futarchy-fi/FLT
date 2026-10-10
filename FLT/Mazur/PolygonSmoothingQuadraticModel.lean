/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRing
public import Mathlib.RingTheory.AdjoinRoot

/-!
# A monic quadratic model for the smoothing chart

Writing s = x + y realizes xy = t as the monic equation y² - sy + t = 0
over R[s]. This works even when the coefficient ring has zero divisors.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R]

/-- The monic equation over the affine sum-coordinate line. -/
def sumQuadratic (t : R) : R[X][X] := X ^ 2 - C X * X + C (C t)

/-- The sum-coordinate equation is monic over every coefficient ring. -/
theorem sumQuadratic_monic (t : R) : (sumQuadratic t).Monic := by
  apply monic_of_degree_le 2
  · unfold sumQuadratic
    compute_degree
    norm_num
  · simp [sumQuadratic, coeff_mul_X]

/-- The actual monic-root algebra over the sum-coordinate line. -/
abbrev QuadraticModel (t : R) := AdjoinRoot (sumQuadratic t)

/-- The sum coordinate in the quadratic model. -/
def sumCoordinate (t : R) : QuadraticModel t := AdjoinRoot.of (sumQuadratic t) X

/-- The chosen root is the original second branch coordinate. -/
def quadraticRoot (t : R) : QuadraticModel t := AdjoinRoot.root (sumQuadratic t)

/-- The root satisfies the original quadratic equation, with its arithmetic constant. -/
theorem quadraticRoot_relation (t : R) :
    quadraticRoot t ^ 2 - sumCoordinate t * quadraticRoot t +
      algebraMap R (QuadraticModel t) t = 0 := by
  have h := AdjoinRoot.eval₂_root (sumQuadratic t)
  change (X ^ 2 - C X * X + C (C t)).eval₂ (AdjoinRoot.of (sumQuadratic t))
    (quadraticRoot t) = 0 at h
  simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C] at h
  exact h

/-- The original chart maps to the quadratic model by x = s-y. -/
def chartToQuadratic (t : R) : ChartRing t →ₐ[R] QuadraticModel t :=
  evaluate t (sumCoordinate t - quadraticRoot t) (quadraticRoot t) (by
    have h := quadraticRoot_relation t
    linear_combination -h)

/-- The first coordinate retains its sum-minus-root expression. -/
@[simp] theorem chartToQuadratic_left (t : R) :
    chartToQuadratic t (leftCoordinate t) = sumCoordinate t - quadraticRoot t :=
  evaluate_left ..

/-- The second coordinate is the actual quadratic root. -/
@[simp] theorem chartToQuadratic_right (t : R) :
    chartToQuadratic t (rightCoordinate t) = quadraticRoot t := evaluate_right ..

/-- Evaluation of the sum-coordinate polynomial at the original x+y. -/
def sumEvaluation (t : R) : R[X] →ₐ[R] ChartRing t :=
  aeval (leftCoordinate t + rightCoordinate t)

/-- The original second coordinate solves the monic equation after sum evaluation. -/
theorem sumEvaluation_root (t : R) :
    (sumQuadratic t).eval₂ (sumEvaluation t) (rightCoordinate t) = 0 := by
  simp only [sumQuadratic, eval₂_add, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C,
    sumEvaluation, AlgHom.coe_toRingHom, aeval_X, aeval_C]
  have h := coordinate_relation t
  linear_combination -h

/-- The quadratic model maps back to the original smoothing quotient. -/
def quadraticToChart (t : R) : QuadraticModel t →ₐ[R] ChartRing t :=
  AdjoinRoot.liftAlgHom (sumQuadratic t) (sumEvaluation t) (rightCoordinate t)
    (sumEvaluation_root t)

/-- The quadratic sum variable maps to the original sum of branch coordinates. -/
@[simp] theorem quadraticToChart_sum (t : R) :
    quadraticToChart t (sumCoordinate t) = leftCoordinate t + rightCoordinate t := by
  exact (AdjoinRoot.liftAlgHom_of ..).trans (aeval_X _)

/-- The quadratic root maps to the original second coordinate. -/
@[simp] theorem quadraticToChart_root (t : R) :
    quadraticToChart t (quadraticRoot t) = rightCoordinate t :=
  AdjoinRoot.liftAlgHom_root ..

end FLT.Mazur.PolygonSmoothing
