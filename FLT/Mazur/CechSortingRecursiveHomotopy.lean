/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSortingTupleChains

/-!
# Recursive sorting homotopy on integral tuple chains

Cone the sorting defect at the first vertex of each nonempty tuple. The resulting
additive maps give a homotopy from signed sorting to the identity and preserve
vertex support. The recursion proves its own cycle and support conditions.
-/

@[expose] public noncomputable section

universe u

namespace FLT.Mazur.CechSortingRecursiveHomotopy

open CechSortingHomotopyCoordinates CechSortingTupleChains

variable {ι : Type u} [LinearOrder ι]

/-- Cone the sorting defect, corrected by the homotopy in the preceding degree. -/
def H : (n : ℕ) → Chains (ι := ι) n →+ Chains (ι := ι) (n + 1)
  | 0 => 0
  | n + 1 => FreeAbelianGroup.lift fun a ↦
      cone (a 0) (n + 1)
        (FreeAbelianGroup.of a - P (n + 1) (FreeAbelianGroup.of a) -
          H n (boundary n (FreeAbelianGroup.of a)))

@[simp]
lemma H_zero (z : Chains (ι := ι) 0) : H 0 z = 0 := rfl

/-- The defining recursion on a nonempty tuple, including repeated vertices. -/
lemma H_succ_of (n : ℕ) (a : Fin (n + 1) → ι) :
    H (n + 1) (FreeAbelianGroup.of a) =
      cone (a 0) (n + 1)
        (FreeAbelianGroup.of a - P (n + 1) (FreeAbelianGroup.of a) -
          H n (boundary n (FreeAbelianGroup.of a))) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The homotopy vanishes on singleton chains. -/
@[simp]
lemma H_one (z : Chains (ι := ι) 1) : H 1 z = 0 := by
  have h : H (ι := ι) 1 = 0 := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change H 1 (FreeAbelianGroup.of a) = 0
    rw [H_succ_of, P_one, H_zero, sub_self, sub_zero, map_zero]
  exact DFunLike.congr_fun h z

/-- The differential equation and support preservation follow together by recursion. -/
lemma H_properties (n : ℕ) :
    (∀ z : Chains (ι := ι) (n + 1),
      boundary (n + 1) (H (n + 1) z) + H n (boundary n z) = z - P (n + 1) z) ∧
    (∀ (S : Set ι) (z : Chains (ι := ι) (n + 1)),
      z ∈ supported S (n + 1) → H (n + 1) z ∈ supported S (n + 2)) := by
  induction n with
  | zero =>
    constructor
    · intro z
      simp
    · intro S z _
      rw [H_one]
      exact (supported S 2).zero_mem
  | succ n ih =>
    have hcycle (z : Chains (ι := ι) (n + 2)) :
        boundary (n + 1) (z - P (n + 2) z - H (n + 1) (boundary (n + 1) z)) = 0 := by
      have hd := ih.1 (boundary (n + 1) z)
      rw [boundary_sq, map_zero, add_zero] at hd
      rw [map_sub, map_sub, boundary_P, hd, sub_self]
    constructor
    · intro z
      induction z using FreeAbelianGroup.induction_on with
      | zero => simp
      | of a =>
        rw [H_succ_of, boundary_cone_of_cycle _ _ _ (hcycle _)]
        abel
      | neg z hz => simp only [map_neg]; rw [← neg_add, hz]; abel
      | add x y hx hy => simp only [map_add]; rw [add_add_add_comm, hx, hy]; abel
    · intro S z hz
      have hs : supported S (n + 2) ≤ (supported S (n + 3)).comap (H (n + 2)) := by
        apply (AddSubgroup.closure_le _).mpr
        rintro _ ⟨a, ha, rfl⟩
        change H (n + 2) (FreeAbelianGroup.of a) ∈ supported S (n + 3)
        rw [H_succ_of]
        apply cone_mem_supported S (a 0) (ha 0)
        have hg := of_mem_supported S (n + 2) a ha
        exact (supported S (n + 2)).sub_mem
          ((supported S (n + 2)).sub_mem hg (P_mem_supported S _ _ hg))
          (ih.2 S _ (boundary_mem_supported S _ _ hg))
      exact hs hz

/-- The sorting homotopy identity in every nonempty tuple length. -/
lemma boundary_H_add_H_boundary (n : ℕ) (z : Chains (ι := ι) (n + 1)) :
    boundary (n + 1) (H (n + 1) z) + H n (boundary n z) = z - P (n + 1) z :=
  (H_properties n).1 z

/-- The homotopy identity at the augmentation term. -/
lemma boundary_H_zero (z : Chains (ι := ι) 0) :
    boundary 0 (H 0 z) = z - P 0 z := by
  simp

/-- The recursively corrected sorting defect is always a cycle. -/
lemma sorting_defect_cycle (n : ℕ) (z : Chains (ι := ι) (n + 1)) :
    boundary n (z - P (n + 1) z - H n (boundary n z)) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have hd := boundary_H_add_H_boundary n (boundary (n + 1) z)
    rw [boundary_sq, map_zero, add_zero] at hd
    rw [map_sub, map_sub, boundary_P, hd, sub_self]

/-- The recursive homotopy preserves support in every tuple length. -/
lemma H_mem_supported (S : Set ι) (n : ℕ) (z : Chains (ι := ι) n)
    (hz : z ∈ supported S n) : H n z ∈ supported S (n + 1) := by
  cases n with
  | zero =>
    rw [H_zero]
    exact (supported S 1).zero_mem
  | succ n => exact (H_properties n).2 S z hz

end FLT.Mazur.CechSortingRecursiveHomotopy
