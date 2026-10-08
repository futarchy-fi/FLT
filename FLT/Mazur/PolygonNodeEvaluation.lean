/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonNodeScalarExtension
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.LinearCombination

/-!
# Evaluating the existing two-branch node algebra

Any two elements with product zero give an algebra map from the polynomial
pair model. This universal property connects actual equation charts to the
node model already used by the polygon geometry.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PolygonNodeEvaluation

open PolygonNodeEqualizer PolygonNodeLocalization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (u v : S) (huv : u * v = 0)

include huv in
/-- Cross terms in evaluations on separate branches are determined by constant terms. -/
theorem cross_evaluation (P Q : R[X]) :
    aeval u P * aeval v Q =
      aeval u P * algebraMap R S (Q.eval 0) +
        algebraMap R S (P.eval 0) * aeval v Q -
        algebraMap R S (P.eval 0) * algebraMap R S (Q.eval 0) := by
  have hd (F : R[X]) : X ∣ F - C (F.eval 0) := by
    rw [X_dvd_iff]
    simp [coeff_zero_eq_eval_zero]
  obtain ⟨P', hP⟩ := hd P
  obtain ⟨Q', hQ⟩ := hd Q
  have hp : aeval u P - algebraMap R S (P.eval 0) = u * aeval u P' := by
    simpa only [map_sub, map_mul, aeval_C, aeval_X] using congrArg (aeval u) hP
  have hq : aeval v Q - algebraMap R S (Q.eval 0) = v * aeval v Q' := by
    simpa only [map_sub, map_mul, aeval_C, aeval_X] using congrArg (aeval v) hQ
  have hz : (aeval u P - algebraMap R S (P.eval 0)) *
      (aeval v Q - algebraMap R S (Q.eval 0)) = 0 := by
    rw [hp, hq]
    calc
      (u * aeval u P') * (v * aeval v Q') = (u * v) * (aeval u P' * aeval v Q') := by ring
      _ = 0 := by rw [huv, zero_mul]
  linear_combination hz

/-- Evaluate a node function by summing its branches and subtracting their common value. -/
def evaluation : A (R := R) →ₐ[R] S where
  toFun z := aeval u (first z) + aeval v (second z) - algebraMap R S ((first z).eval 0)
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by simp only [map_add, eval_add]; ring
  map_mul' z w := by
    have hz : (first z).eval 0 = (second z).eval 0 := z.property
    have hw : (first w).eval 0 = (second w).eval 0 := w.property
    have hzw := cross_evaluation u v huv (first z) (second w)
    have hwz := cross_evaluation u v huv (first w) (second z)
    simp only [← hz, ← hw] at hzw hwz
    simp only [map_mul, eval_mul]
    linear_combination -hzw - hwz
  commutes' r := by simp [AlgHom.commutes]

/-- This evaluation has the stated reconstruction formula. -/
theorem evaluation_apply (z : A (R := R)) :
    evaluation u v huv z =
      aeval u (first z) + aeval v (second z) - algebraMap R S ((first z).eval 0) := rfl

/-- The first branch generator evaluates to the first supplied element. -/
@[simp] theorem evaluation_x : evaluation (R := R) u v huv x = u := by
  simp [evaluation_apply]

/-- The second branch generator evaluates to the second supplied element. -/
@[simp] theorem evaluation_y : evaluation (R := R) u v huv y = v := by
  simp [evaluation_apply]

/-- Evaluation at the universal two branches recovers every node function. -/
theorem evaluation_self : evaluation (x (R := R)) y x_mul_y = AlgHom.id R _ := by
  apply AlgHom.ext
  intro z
  exact PolygonNodeScalarExtension.reconstruct z

end FLT.Mazur.PolygonNodeEvaluation
