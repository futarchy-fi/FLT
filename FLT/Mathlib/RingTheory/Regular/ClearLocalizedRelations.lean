/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.UnitMultiples
public import Mathlib.RingTheory.Localization.Ideal

/-! # Clear localized regular relations inside their original ideal -/

@[expose] public noncomputable section

namespace RingTheory.Sequence

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (T : Submonoid R) [IsLocalization T S]

include T in
/-- Relations in an extended ideal can be replaced by original-ideal numerators.
Their localized ideal, order, length and regularity are unchanged. -/
theorem exists_numerators_of_localized_regular_list (I : Ideal R) (rs : List S)
    (hmem : ∀ x ∈ rs, x ∈ I.map (algebraMap R S)) (hreg : IsRegular S rs) :
    ∃ qs : List R, (∀ q ∈ qs, q ∈ I) ∧ qs.length = rs.length ∧
      Ideal.ofList (qs.map (algebraMap R S)) = Ideal.ofList rs ∧
      IsRegular S (qs.map (algebraMap R S)) := by
  classical
  have repr (x : S) : ∃ d : I × T,
      x ∈ rs → x * algebraMap R S d.2 = algebraMap R S d.1 := by
    by_cases hx : x ∈ rs
    · obtain ⟨d, hd⟩ := (IsLocalization.mem_map_algebraMap_iff T S).mp (hmem x hx)
      exact ⟨d, fun _ ↦ hd⟩
    · exact ⟨⟨0, 1⟩, fun h ↦ (hx h).elim⟩
  choose d hd using repr
  let qs := rs.map fun x ↦ ((d x).1 : R)
  let u (x : S) := algebraMap R S (d x).2
  have hu (x : S) (_ : x ∈ rs) : IsUnit (u x) := IsLocalization.map_units S (d x).2
  have hqs : qs.map (algebraMap R S) = rs.map (fun x ↦ u x * x) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact (hd x hx).symm.trans (mul_comm _ _)
  refine ⟨qs, ?_, by simp [qs], ?_, ?_⟩
  · intro q hq
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hq
    exact (d x).1.property
  · rw [hqs, Ideal.ofList_map_unit_mul rs u hu]
  · rw [hqs, isRegular_map_unit_mul_iff rs u hu]
    exact hreg

end RingTheory.Sequence
