/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionLiftIdeal

/-!
# Multipliers for algebraic combinations of lifted sections

Products of actual lifting multipliers give explicit lifts of sums and
products. No choice of invariant coefficients in a source certificate is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

/-- A section already in the image has every multiplier available. -/
theorem sectionLiftIdeal_image (a : A) : sectionLiftIdeal f (f a) = ⊤ :=
  (sectionLiftIdeal_eq_top_iff f _).mpr ⟨a, rfl⟩

/-- Negation preserves the actual multiplier ideal. -/
theorem sectionLiftIdeal_neg (t : B) :
    sectionLiftIdeal f (-t) = sectionLiftIdeal f t := by
  ext s
  constructor <;> rintro ⟨a, ha⟩
  · exact ⟨-a, by rw [map_neg, ha, mul_neg, neg_neg]⟩
  · exact ⟨-a, by rw [map_neg, ha, mul_neg]⟩

/-- Multiplying two lifting multipliers supplies a multiplier for the sum. -/
theorem sectionLiftIdeal_mul_le_add (t u : B) :
    sectionLiftIdeal f t * sectionLiftIdeal f u ≤ sectionLiftIdeal f (t + u) := by
  apply Ideal.mul_le.mpr
  rintro s ⟨a, ha⟩ v ⟨b, hb⟩
  refine ⟨v * a + s * b, ?_⟩
  simp only [map_add, map_mul, ha, hb]
  ring

/-- Products of actual lifts give lifts of products with multiplied denominators. -/
theorem sectionLiftIdeal_mul_le_mul (t u : B) :
    sectionLiftIdeal f t * sectionLiftIdeal f u ≤ sectionLiftIdeal f (t * u) := by
  apply Ideal.mul_le.mpr
  rintro s ⟨a, ha⟩ v ⟨b, hb⟩
  refine ⟨a * b, ?_⟩
  simp only [map_mul, ha, hb]
  ring

/-- Powers of the multiplier ideal lift the same powers of the section. -/
theorem sectionLiftIdeal_pow_le (t : B) (n : ℕ) :
    sectionLiftIdeal f t ^ n ≤ sectionLiftIdeal f (t ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, ← map_one f, sectionLiftIdeal_image]
    exact le_top
  | succ n hn =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono hn le_rfl).trans (sectionLiftIdeal_mul_le_mul f _ _)

/-- A lift of a unit times its denominator reverses roles when lifting the inverse. -/
theorem sectionLiftIdeal_inverse_multiplier {t u : B} (htu : t * u = 1)
    {s a : A} (ha : f a = f s * t) : a ∈ sectionLiftIdeal f u := by
  refine ⟨s, ?_⟩
  rw [ha, mul_assoc, htu, mul_one]

end FLT.Mazur
