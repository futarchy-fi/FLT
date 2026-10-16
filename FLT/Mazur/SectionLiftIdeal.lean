/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# The ideal of multipliers admitting a section lift

For a ring map and a fixed target section, the multipliers whose products lift
form an actual ideal of the source ring. Its radical records finite-power
lifting; no surjectivity or vanishing hypothesis is built into the definition.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

/-- Source multipliers making the given target element lift. -/
def sectionLiftIdeal (t : B) : Ideal A where
  carrier := {s | ∃ a, f a = f s * t}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro s u ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simp only [map_add, ha, hb, add_mul]⟩
  smul_mem' := by
    rintro c s ⟨a, ha⟩
    exact ⟨c * a, by simp only [smul_eq_mul, map_mul, ha, mul_assoc]⟩

/-- Membership is the actual original lifting equation. -/
theorem mem_sectionLiftIdeal (t : B) (s : A) :
    s ∈ sectionLiftIdeal f t ↔ ∃ a, f a = f s * t := Iff.rfl

/-- Radical membership is precisely finite-power lifting. -/
theorem mem_sectionLiftIdeal_radical (t : B) (s : A) :
    s ∈ (sectionLiftIdeal f t).radical ↔ ∃ (n : ℕ) (a : A), f a = f s ^ n * t := by
  simp only [Ideal.mem_radical_iff, mem_sectionLiftIdeal, map_pow]

/-- The ideal is the unit ideal exactly when the section already lifts. -/
theorem sectionLiftIdeal_eq_top_iff (t : B) :
    sectionLiftIdeal f t = ⊤ ↔ ∃ a, f a = t := by
  rw [Ideal.eq_top_iff_one]
  simp only [mem_sectionLiftIdeal, map_one, one_mul]

/-- Subtracting a known lift leaves exactly the same obstruction ideal. -/
theorem sectionLiftIdeal_sub_image (t : B) (a : A) :
    sectionLiftIdeal f (t - f a) = sectionLiftIdeal f t := by
  ext s
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b + s * a, ?_⟩
    rw [map_add, map_mul, hb, mul_sub, sub_add_cancel]
  · rintro ⟨b, hb⟩
    exact ⟨b - s * a, by rw [map_sub, map_mul, hb, mul_sub]⟩

/-- Two simultaneous lifting multipliers also lift the sum. -/
theorem sectionLiftIdeal_inf_le_add (t u : B) :
    sectionLiftIdeal f t ⊓ sectionLiftIdeal f u ≤ sectionLiftIdeal f (t + u) := by
  rintro s ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add, ha, hb, mul_add]⟩

/-- Multiplying a target section by an original scalar preserves every lifting multiplier. -/
theorem sectionLiftIdeal_le_mul_image (t : B) (a : A) :
    sectionLiftIdeal f t ≤ sectionLiftIdeal f (f a * t) := by
  rintro s ⟨b, hb⟩
  refine ⟨a * b, ?_⟩
  rw [map_mul, hb, mul_left_comm]

end FLT.Mazur
