/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The exact scalar ideal of homogeneous numerator obstructions

For a ring map and a prescribed source ideal, the admissible scalars are
those whose multiple of the target value has a numerator in that ideal.
The quotient is cyclic, but finite generation alone does not put any chosen
parameter in the radical of the scalar ideal.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HomogeneousNumeratorObstruction
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Scalars admitting an actual numerator in the prescribed homogeneous ideal. -/
def scalarIdeal (f : R →+* S) (I : Ideal R) (x : S) : Ideal R where
  carrier := {a | ∃ z ∈ I, f z = f a * x}
  zero_mem' := ⟨0, I.zero_mem, by rw [map_zero, zero_mul]⟩
  add_mem' := by
    rintro a b ⟨z, hz, he⟩ ⟨w, hw, hf⟩
    exact ⟨z + w, I.add_mem hz hw, by rw [map_add, he, hf, map_add, add_mul]⟩
  smul_mem' := by
    rintro a b ⟨z, hz, he⟩
    exact ⟨a * z, I.mul_mem_left a hz, by
      change f (a * z) = f (a * b) * x
      rw [map_mul, he, map_mul, mul_assoc]⟩

/-- This is membership in the source-module image, with no target ideal closure. -/
theorem mem_scalarIdeal (f : R →+* S) (I : Ideal R) (x : S) (a : R) :
    a ∈ scalarIdeal f I x ↔ ∃ z ∈ I, f z = f a * x := Iff.rfl

/-- The unit scalar is admissible exactly when the original unscaled value lifts. -/
theorem one_mem_scalarIdeal (f : R →+* S) (I : Ideal R) (x : S) :
    1 ∈ scalarIdeal f I x ↔ ∃ z ∈ I, f z = x := by
  simp only [mem_scalarIdeal, map_one, one_mul]

/-- One power in this ideal is precisely a bounded homogeneous numerator. -/
theorem mem_radical_scalarIdeal (f : R →+* S) (I : Ideal R) (x : S) (r : R) :
    r ∈ (scalarIdeal f I x).radical ↔
      ∃ (N : ℕ) (z : R), z ∈ I ∧ f z = f r ^ N * x := by
  simp only [Ideal.mem_radical_iff, mem_scalarIdeal, map_pow]

/-- The exact obstruction quotient; its distinguished class is the class of one. -/
abbrev ScalarQuotient (f : R →+* S) (I : Ideal R) (x : S) := R ⧸ scalarIdeal f I x

/-- This module is cyclic, independent of any Noetherian hypothesis. -/
theorem scalarQuotient_finite (f : R →+* S) (I : Ideal R) (x : S) :
    Module.Finite R (ScalarQuotient f I x) := inferInstance

/-- Vanishing of a scalar class retains the exact original numerator condition. -/
theorem quotient_eq_zero_iff (f : R →+* S) (I : Ideal R) (x : S) (a : R) :
    Ideal.Quotient.mk (scalarIdeal f I x) a = 0 ↔
      ∃ z ∈ I, f z = f a * x :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Unscaled lifting is equivalent to vanishing of the distinguished obstruction. -/
theorem quotient_one_eq_zero_iff (f : R →+* S) (I : Ideal R) (x : S) :
    (1 : ScalarQuotient f I x) = 0 ↔ ∃ z ∈ I, f z = x := by
  rw [← map_one (Ideal.Quotient.mk (scalarIdeal f I x)), quotient_eq_zero_iff,
    map_one, one_mul]

end FLT.Mazur.HomogeneousNumeratorObstruction
