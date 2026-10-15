/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticResidueNilpotence

/-!
# The exact original residue coefficient kernel

A parameter generating the maximal ideal also generates the kernel of every
arithmetic stage's original residue map. This uses no residue coefficient field
inside the integral ring.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.PolygonArithmeticStages
variable (A : Type*) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : maximalIdeal A = ideal A π)
  (hπ : algebraMap A (ResidueField A) π = 0) (m : ℕ)

include hgen in
/-- The original residue kernel consists of exactly the parameter multiples. -/
theorem residueMap_eq_zero_iff (z : Quotient A π m) :
    residueMap A π hπ m z = 0 ↔ ∃ w, parameter A π m * w = z := by
  constructor
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change residue A a = 0 → _
    rw [residue_eq_zero_iff, hgen]
    change a ∈ Ideal.span {π} → _
    rw [Ideal.mem_span_singleton]
    rintro ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk _ b, by rw [map_mul]; rfl⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, residueMap_parameter, zero_mul]

include hgen in
/-- The original residue map has the actual principal parameter ideal as kernel. -/
theorem residueMap_ker : RingHom.ker (residueMap A π hπ m) =
    Ideal.span {parameter A π m} := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (residueMap_eq_zero_iff A π hgen hπ m z).trans (exists_congr fun _ ↦ eq_comm)

end FLT.Mazur.PolygonArithmeticStages
