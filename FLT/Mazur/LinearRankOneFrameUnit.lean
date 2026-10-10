/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The unit relating two actual rank-one frames

A scalar-module automorphism is multiplication by its value at one, and
that value is a unit. Consequently any two frames of a rank-one module
have an explicitly constructed unit transition, over an arbitrary ring.
-/

@[expose] public noncomputable section
universe u v
namespace FLT.Mazur.LinearRankOneFrameUnit
variable {R : Type u} [CommRing R]

/-- The inverse image of one supplies an inverse to the scalar automorphism's value at one. -/
lemma inv_one_mul_one (e : R ≃ₗ[R] R) : e.symm 1 * e 1 = 1 := by
  simpa only [smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply] using
    (e.map_smul (e.symm 1) (1 : R)).symm

/-- The actual coordinate multiplier of an automorphism of the scalar module. -/
def scalarUnit (e : R ≃ₗ[R] R) : Rˣ where
  val := e 1
  inv := e.symm 1
  val_inv := (mul_comm _ _).trans (inv_one_mul_one e)
  inv_val := inv_one_mul_one e

/-- The unit's scalar action recovers the original automorphism on every element. -/
lemma scalarUnit_apply (e : R ≃ₗ[R] R) (a : R) :
    e a = a * (scalarUnit e : R) := by
  simpa only [scalarUnit, smul_eq_mul, mul_one] using e.map_smul a (1 : R)

variable {P : Type v} [AddCommGroup P] [Module R P]

/-- The genuine transition unit between two frames of the same rank-one module. -/
def frameUnit (e d : P ≃ₗ[R] R) : Rˣ := scalarUnit (d.symm.trans e)

/-- The new generator is the old generator multiplied by the constructed unit. -/
lemma frame_generator (e d : P ≃ₗ[R] R) :
    d.symm 1 = (frameUnit e d : R) • e.symm 1 := by
  apply e.injective
  rw [e.map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  rfl

/-- Every original linear inclusion preserves the actual frame-transition formula. -/
lemma frame_image {Q : Type*} [AddCommGroup Q] [Module R Q]
    (s : P →ₗ[R] Q) (e d : P ≃ₗ[R] R) :
    s (d.symm 1) = (frameUnit e d : R) • s (e.symm 1) := by
  rw [frame_generator e d, s.map_smul]

end FLT.Mazur.LinearRankOneFrameUnit
