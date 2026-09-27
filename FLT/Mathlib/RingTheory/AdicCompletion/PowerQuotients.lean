/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Equality detected by ideal-power quotients

In an adically separated ring, equality can be checked modulo every power of the ideal.
-/

@[expose] public section

/-- Elements of an adically separated ring are equal if their images in every
ideal-power quotient agree. -/
theorem eq_of_all_power_quotients {R : Type*} [CommRing R]
    (I : Ideal R) [IsHausdorff I R] {x y : R}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) :
    x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simpa using! h n
