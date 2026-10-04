/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence

/-! # Multiplying individual relations by units -/

@[expose] public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Ideal

/-- Changing each relation by a unit multiple leaves its ideal unchanged. -/
theorem ofList_map_unit_mul (rs : List R) (u : R → R) (hu : ∀ x ∈ rs, IsUnit (u x)) :
    ofList (rs.map fun x ↦ u x * x) = ofList rs := by
  induction rs with
  | nil => simp
  | cons x rs ih =>
    simp only [List.map_cons, ofList_cons]
    rw [span_singleton_mul_left_unit (hu x (by simp)), ih (fun y hy ↦ hu y (by simp [hy]))]

end Ideal

namespace RingTheory.Sequence

/-- Unit multiples preserve every prefix quotient and hence weak regularity. -/
theorem isWeaklyRegular_map_unit_mul_iff (rs : List R) (u : R → R)
    (hu : ∀ x ∈ rs, IsUnit (u x)) :
    IsWeaklyRegular M (rs.map fun x ↦ u x * x) ↔ IsWeaklyRegular M rs := by
  simp only [isWeaklyRegular_iff, List.length_map, List.getElem_map]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [← List.map_take, Ideal.ofList_map_unit_mul _ u
    (fun x hx ↦ hu x (List.mem_of_mem_take hx))]
  exact ((hu rs[i] (List.getElem_mem hi)).isSMulRegular
    (M := M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M))).mul_iff_right

/-- Unit multiples preserve regularity, including the nonzero terminal quotient. -/
theorem isRegular_map_unit_mul_iff (rs : List R) (u : R → R)
    (hu : ∀ x ∈ rs, IsUnit (u x)) :
    IsRegular M (rs.map fun x ↦ u x * x) ↔ IsRegular M rs := by
  rw [isRegular_iff, isRegular_iff, isWeaklyRegular_map_unit_mul_iff rs u hu,
    Ideal.ofList_map_unit_mul rs u hu]

end RingTheory.Sequence
