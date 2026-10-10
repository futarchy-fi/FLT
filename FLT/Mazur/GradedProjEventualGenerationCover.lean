/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Eventual homogeneous ideal generation covers Proj

A family whose ideal contains every sufficiently high homogeneous degree
covers Proj by its basic opens. Raising any positive homogeneous element
to a sufficiently large power proves the required radical containment.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.GradedProjEventualGenerationCover

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Containment of every sufficiently high degree suffices for a family of Proj basic opens. -/
theorem iSup_basicOpen_eq_top {ι : Type*} (f : ι → A) (B : ℕ)
    (hB : ∀ d ≥ B, ∀ a ∈ 𝒜 d, a ∈ Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  classical
  refine top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [Proj.mem_basicOpen, Decidable.not_not] at H
  have hspan : Ideal.span (Set.range f) ≤ x.asHomogeneousIdeal.toIdeal := by
    rwa [Ideal.span_le, Set.range_subset_iff]
  apply x.not_irrelevant_le
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro d hd a ha
  change a ∈ 𝒜 d at ha
  have hp : a ^ (B + 1) ∈ 𝒜 ((B + 1) * d) := by
    simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded (B + 1) ha
  have hb : B ≤ (B + 1) * d :=
    (Nat.le_succ B).trans (Nat.le_mul_of_pos_right (B + 1) hd)
  exact x.isPrime.mem_of_pow_mem (B + 1) (hspan (hB _ hb _ hp))

end FLT.Mazur.GradedProjEventualGenerationCover
