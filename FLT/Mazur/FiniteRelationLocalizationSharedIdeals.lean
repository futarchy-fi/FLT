/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalIdealPatching
public import FLT.Mazur.FiniteRelationLocalizationExactIdeals

/-!
# Simultaneous exact kernels on distinct principal opens

Compatible finite ideals killed in the original chart can all be realized as
transition kernels using one shared ambient relation set. Compatibility is
the usual denominator-power membership condition on pairwise intersections;
it prevents the naive union from introducing extra localized relations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) {ι : Type w} [Finite ι] (r : ι → P)

/-- Localized ideals satisfying overlap compatibility have exact shared ambient realizations. -/
theorem exists_shared_transition_ker_eq (s : Finset I)
    (J : ∀ i, Ideal (Stage I (r i) s)) (hJ : ∀ i, (J i).FG)
    (hkill : ∀ i, J i ≤ RingHom.ker (toQuotient R I (r i) s).toRingHom)
    (hcompat : ∀ i j, ∀ z : I, numerator I (r i) s z ∈ J i →
      ∃ n : ℕ, numerator I (r j) s (r i ^ n * (z : P)) ∈ J j) :
    ∃ (t : Finset I) (hst : s ≤ t),
      ∀ i, RingHom.ker (transition R I (r i) hst).toRingHom = J i := by
  classical
  choose q hsq hq using fun i ↦ exists_transition_ker_eq R I (r i) s (J i) (hJ i) (hkill i)
  let v (i) := (q i).image (Subtype.val : I → P)
  have hvI (i) : ∀ z ∈ v i, z ∈ I := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    exact y.property
  have hv (i) : Ideal.span ((numerator I (r i) s) '' (v i : Set P)) = J i := by
    have hi := hq i
    rw [ker_transition] at hi
    simpa only [v, Finset.coe_image, FiniteRelationModel.relations, Ideal.map_span]
      using hi
  have hc (i) (z : P) (hz : z ∈ v i) (j) :
      ∃ n : ℕ, numerator I (r j) s (r i ^ n * z) ∈ J j := by
    apply hcompat i j ⟨z, hvI i z hz⟩
    rw [← hv i]
    exact Ideal.subset_span ⟨z, hz, rfl⟩
  obtain ⟨t, htI, ht⟩ := PrincipalIdealPatching.exists_finite_generators I r
    (fun i ↦ numerator I (r i) s) (fun i ↦ numerator_denominator_isUnit I (r i) s)
    J v hvI hv hc
  let q' : Finset I := t.attach.image (fun z ↦ ⟨z.val, htI z.val z.property⟩)
  have hq' (z : P) (hz : z ∈ t) : (⟨z, htI z hz⟩ : I) ∈ q' :=
    Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩
  refine ⟨s ∪ q', Finset.subset_union_left, fun i ↦ ?_⟩
  rw [ker_transition]
  change (Ideal.span (Subtype.val '' (↑(s ∪ q') : Set I))).map (numerator I (r i) s) = J i
  rw [Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    rcases Finset.mem_union.mp hy with hy | hy
    · rw [numerator_eq_zero I (r i) s y hy]
      exact (J i).zero_mem
    · obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
      rw [← ht i]
      exact Ideal.subset_span ⟨z.val, z.property, rfl⟩
  · rw [← ht i]
    apply Ideal.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    apply Ideal.subset_span
    exact ⟨z, ⟨⟨z, htI z hz⟩, Finset.mem_union_right _ (hq' z hz), rfl⟩, rfl⟩

end FLT.Mazur.FiniteRelationLocalization
