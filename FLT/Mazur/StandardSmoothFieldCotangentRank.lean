/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Relative dimension from an actual field-valued cotangent space

On a standard-smooth affine chart the differential module is finite free.
Its rank is therefore detected after any field-valued change of coefficients.
This recovers relative dimension from the original algebraic cotangent space.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.StandardSmoothFieldCotangentRank

open TensorProduct

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [Field B]
  [Algebra R A] [Algebra A B] [Algebra.IsStandardSmooth R A]

/-- Any actual field point detects the relative dimension of a standard-smooth chart. -/
theorem relativeDimension_iff (d : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension d R A ↔
      Module.finrank B (B ⊗[A] Ω[A⁄R]) = d := by
  let _ : Nontrivial A := (algebraMap A B).domain_nontrivial
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth,
    Module.finrank_baseChange, ← Module.finrank_eq_rank]
  exact Nat.cast_inj

/-- A one-dimensional actual cotangent space makes the whole standard-smooth chart relative one. -/
theorem relativeDimension_one
    (hr : Module.finrank B (B ⊗[A] Ω[A⁄R]) = 1) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R A :=
  (relativeDimension_iff R A B 1).mpr hr

end FLT.Mazur.StandardSmoothFieldCotangentRank
