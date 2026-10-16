/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseLocalizedBoundaryCorrections
public import Mathlib.RingTheory.Ideal.Basic

/-!
# The ideal computed by simultaneous original boundary corrections

Its elements are original scalars whose full discrepancy is the discrepancy of
an exact boundary-kernel family. Membership is equivalent to an actual scaled
compatible lift. The ideal is independent of the initial chosen boundary lifts.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  (α : ∀ i, R →+* A i) (φ : ∀ i, A i →+* B i)
  (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (hα : ∀ i j x, p i j (α i x) = q i j (α j x)) (u : ∀ i, A i)

/-- An ideal in the original scalar ring, defined using all original discrepancy equations. -/
def ideal : Ideal R where
  carrier := {r | ∃ z : ∀ i, A i, (∀ i, φ i (z i) = 0) ∧ ∀ i j,
    p i j (z i) - q i j (z j) = p i j (α i r) * (p i j (u i) - q i j (u j))}
  zero_mem' := ⟨fun _ ↦ 0, fun i ↦ map_zero _, fun i j ↦ by simp⟩
  add_mem' := by
    rintro r s ⟨z, hz, he⟩ ⟨w, hw, hf⟩
    refine ⟨fun i ↦ z i + w i, fun i ↦ by rw [map_add, hz, hw, add_zero], fun i j ↦ ?_⟩
    simp only [map_add]
    calc
      _ = (p i j (z i) - q i j (z j)) + (p i j (w i) - q i j (w j)) := by ring
      _ = _ := by rw [he, hf]; ring
  smul_mem' := by
    rintro a r ⟨z, hz, he⟩
    refine ⟨fun i ↦ α i a * z i, fun i ↦ by rw [map_mul, hz, mul_zero], fun i j ↦ ?_⟩
    change p i j (α i a * z i) - q i j (α j a * z j) =
      p i j (α i (a * r)) * (p i j (u i) - q i j (u j))
    simp only [map_mul, ← hα]
    rw [← mul_sub, he, mul_assoc]

/-- Membership has an explicit compatible numerator, without any localization. -/
theorem mem_iff_numerators (r : R) :
    r ∈ ideal α φ p q hα u ↔ ∃ w : ∀ i, A i,
      (∀ i, φ i (w i) = φ i (α i r) * φ i (u i)) ∧
      ∀ i j, p i j (w i) = q i j (w j) := by
  constructor
  · rintro ⟨z, hz, he⟩
    refine ⟨fun i ↦ α i r * u i - z i,
      fun i ↦ by rw [map_sub, map_mul, hz, sub_zero], fun i j ↦ ?_⟩
    simp only [map_sub, map_mul, ← hα]
    apply sub_eq_zero.mp
    calc
      _ = p i j (α i r) * (p i j (u i) - q i j (u j)) -
          (p i j (z i) - q i j (z j)) := by ring
      _ = 0 := by rw [he, sub_self]
  · rintro ⟨w, hw, hc⟩
    refine ⟨fun i ↦ α i r * u i - w i,
      fun i ↦ by rw [map_sub, map_mul, hw, sub_self], fun i j ↦ ?_⟩
    simp only [map_sub, map_mul, ← hα, hc i j]
    ring

/-- Changing the initial lift family preserves the computed ideal exactly. -/
theorem ideal_eq_of_boundary_eq (v : ∀ i, A i) (h : ∀ i, φ i (u i) = φ i (v i)) :
    ideal α φ p q hα u = ideal α φ p q hα v := by
  ext r
  simp only [mem_iff_numerators, h]

end FLT.Mazur.BoundaryCorrectionIdeal
