/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Positive homogeneous witnesses to noncontainment

A homogeneous ideal inside the irrelevant ideal has a positive-degree homogeneous
element outside any homogeneous ideal which does not contain it.
-/

@[expose] public section

namespace FLT.Mazur.HomogeneousAvoidance

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Extract a homogeneous component witnessing noncontainment of homogeneous ideals. -/
lemma exists_homogeneous_not_mem (I P : HomogeneousIdeal 𝒜) (h : ¬ I ≤ P) :
    ∃ (n : ℕ) (x : A), x ∈ 𝒜 n ∧ x ∈ I ∧ x ∉ P := by
  obtain ⟨x, hxI, hxP⟩ := Set.not_subset.mp h
  have hn : ∃ n, (DirectSum.decompose 𝒜 x n : A) ∉ P := by
    by_contra! hn
    exact hxP (P.isHomogeneous.mem_iff.mpr hn)
  obtain ⟨n, hn⟩ := hn
  exact ⟨n, _, Subtype.prop _, I.isHomogeneous n hxI, hn⟩

/-- The component can be chosen in positive degree when the source is irrelevant. -/
lemma exists_positive_not_mem (I P : HomogeneousIdeal 𝒜)
    (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜) (h : ¬ I ≤ P) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ x ∉ P := by
  obtain ⟨n, x, hxn, hxI, hxP⟩ := exists_homogeneous_not_mem 𝒜 I P h
  refine ⟨n, x, ?_, hxn, hxI, hxP⟩
  apply Nat.pos_of_ne_zero
  intro hn
  have hz := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 x).mp (hI hxI)
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hn ▸ hxn)] at hz
  exact hxP (hz ▸ P.toIdeal.zero_mem)

end FLT.Mazur.HomogeneousAvoidance
