/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationNumerators

/-!
# Realizing finite ideals exactly by chart relations

Every finitely generated ideal of a principal-open stage killed in the full
quotient is exactly the kernel of a later chart transition. No saturation or
finite generation of the full relation ideal is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- Any finite ideal killed in the limit can be imposed without extra localized relations. -/
theorem exists_transition_ker_eq (s : Finset I) (J : Ideal (Stage I r s)) (hJ : J.FG)
    (h : J ≤ RingHom.ker (toQuotient R I r s).toRingHom) :
    ∃ (t : Finset I) (hst : s ≤ t), RingHom.ker (transition R I r hst).toRingHom = J := by
  classical
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  have hmem (i : Fin n) : x i ∈ J := hx ▸ Ideal.subset_span (Set.mem_range_self i)
  choose z m hm using fun i ↦ exists_relation_numerator R I r s (x i) (h (hmem i))
  let t := s ∪ Finset.univ.image z
  have hst : s ≤ t := Finset.subset_union_left
  have hz (i : Fin n) : z i ∈ t :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  refine ⟨t, hst, le_antisymm ?_ ?_⟩
  · rw [ker_transition]
    change (Ideal.span (Subtype.val '' (t : Set I))).map (numerator I r s) ≤ J
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    rcases Finset.mem_union.mp hq with hq | hq
    · rw [numerator_eq_zero I r s q hq]
      exact J.zero_mem
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (numerator_mem_iff I r s J (x i) (z i) (m i) (hm i)).mpr (hmem i)
  · rw [← hx]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (numerator_mem_iff I r s (RingHom.ker (transition R I r hst).toRingHom)
      (x i) (z i) (m i) (hm i)).mp
    change transition R I r hst (numerator I r s (z i)) = 0
    rw [transition_numerator, numerator_eq_zero I r t (z i) (hz i)]

end FLT.Mazur.FiniteRelationLocalization
