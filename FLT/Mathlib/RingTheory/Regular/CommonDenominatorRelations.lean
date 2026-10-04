/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.UnitMultiples
public import Mathlib.RingTheory.Localization.Ideal

/-! # Clear relation denominators while retaining regularity after reduction -/

@[expose] public noncomputable section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (T : Submonoid R) [IsLocalization T S]

/-- A list in an extended ideal has original-ideal numerators with one common denominator. -/
theorem exists_common_denominator_list (I : Ideal R) (rs : List S)
    (hmem : ∀ x ∈ rs, x ∈ I.map (algebraMap R S)) :
    ∃ (d : T) (qs : List R), (∀ q ∈ qs, q ∈ I) ∧ qs.length = rs.length ∧
      qs.map (algebraMap R S) = rs.map (fun x ↦ algebraMap R S d * x) := by
  induction rs with
  | nil => exact ⟨1, [], by simp, rfl, rfl⟩
  | cons x rs ih =>
    obtain ⟨⟨a, d⟩, hd⟩ := (IsLocalization.mem_map_algebraMap_iff T S).mp
      (hmem x (by simp))
    obtain ⟨e, qs, hqs, hlen, he⟩ := ih (fun y hy ↦ hmem y (by simp [hy]))
    refine ⟨d * e, (e * a : R) :: qs.map (fun q ↦ d * q), ?_, by simp [hlen], ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact I.mul_mem_left _ a.property
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
        exact I.mul_mem_left _ (hqs b hb)
    · simp only [List.map_cons, List.map_map, Submonoid.coe_mul, map_mul]
      congr 1
      · rw [← hd]
        ring
      · have h := congrArg (List.map (fun y : S ↦ algebraMap R S d * y)) he
        simpa only [List.map_map, Function.comp_def, map_mul, mul_assoc] using h

include T in
/-- Clearing denominators keeps the local ideal and any regular reduction of the list.
This does not assert regularity upstairs. -/
theorem exists_numerators_of_regular_image {U : Type*} [CommRing U]
    (I : Ideal R) (rs : List S) (φ : S →+* U)
    (hmem : ∀ x ∈ rs, x ∈ I.map (algebraMap R S))
    (hreg : RingTheory.Sequence.IsRegular U (rs.map φ)) :
    ∃ qs : List R, (∀ q ∈ qs, q ∈ I) ∧ qs.length = rs.length ∧
      Ideal.ofList (qs.map (algebraMap R S)) = Ideal.ofList rs ∧
      RingTheory.Sequence.IsRegular U ((qs.map (algebraMap R S)).map φ) := by
  obtain ⟨d, qs, hqs, hlen, he⟩ := I.exists_common_denominator_list T rs hmem
  have hu : IsUnit (algebraMap R S d) := IsLocalization.map_units S d
  refine ⟨qs, hqs, hlen, ?_, ?_⟩
  · rw [he, Ideal.ofList_map_unit_mul rs (fun _ ↦ algebraMap R S d) (fun _ _ ↦ hu)]
  · rw [he]
    have hlist : (rs.map (fun x ↦ algebraMap R S d * x)).map φ =
        (rs.map φ).map (fun x ↦ φ (algebraMap R S d) * x) := by
      simp only [List.map_map, Function.comp_def, map_mul]
    rw [hlist, RingTheory.Sequence.isRegular_map_unit_mul_iff
      (rs.map φ) (fun _ ↦ φ (algebraMap R S d)) (fun _ _ ↦ hu.map φ)]
    exact hreg

end Ideal
