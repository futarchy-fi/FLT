/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Maximal

/-!
# The exact original scalar ideal of full-relation boundary lifts

For a fixed boundary coefficient, admissible original scalars form an ideal.
Consequently local solvability at every original maximal ideal patches to an
unscaled global compatible lift. This does not assert local solvability.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalScalarRelationLiftIdeal
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  (σ : R →+* A) (β : A →+* B) (F H : A →+* C)
  (hσ : ∀ r, F (σ r) = H (σ r))

/-- Original scalars admitting a numerator with its exact boundary and full relation equation. -/
def liftIdeal (t : B) : Ideal R where
  carrier := {r | ∃ w : A, β w = β (σ r) * t ∧ F w = H w}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro r s ⟨u, hu, heu⟩ ⟨v, hv, hev⟩
    refine ⟨u + v, ?_, ?_⟩
    · simp only [map_add, hu, hv, add_mul]
    · simp only [map_add, heu, hev]
  smul_mem' := by
    rintro r s ⟨w, hw, he⟩
    refine ⟨σ r * w, ?_, ?_⟩
    · simp only [smul_eq_mul, map_mul, hw, mul_assoc]
    · simp only [map_mul, hσ, he]

/-- Ideal membership retains both equations on the original rings. -/
theorem mem_liftIdeal (t : B) (r : R) :
    r ∈ liftIdeal σ β F H hσ t ↔
      ∃ w : A, β w = β (σ r) * t ∧ F w = H w := Iff.rfl

/-- A global exact compatible lift is equivalent to the unit ideal. -/
theorem liftIdeal_eq_top_iff (t : B) :
    liftIdeal σ β F H hσ t = ⊤ ↔ ∃ w : A, β w = t ∧ F w = H w := by
  rw [Ideal.eq_top_iff_one, mem_liftIdeal]
  simp only [map_one, one_mul]

include hσ in
/-- Local numerators at every original maximal ideal patch to an exact global lift. -/
theorem exists_lift_of_maximal (t : B)
    (h : ∀ P : Ideal R, P.IsMaximal → ∃ r : R, r ∉ P ∧
      ∃ w : A, β w = β (σ r) * t ∧ F w = H w) :
    ∃ w : A, β w = t ∧ F w = H w := by
  apply (liftIdeal_eq_top_iff σ β F H hσ t).mp
  by_contra hn
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (liftIdeal σ β F H hσ t) hn
  obtain ⟨r, hr, w, hw, he⟩ := h P hP
  exact hr (hle ⟨w, hw, he⟩)

end FLT.Mazur.OriginalScalarRelationLiftIdeal
