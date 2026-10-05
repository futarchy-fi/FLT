/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Positive homogeneous basic neighborhoods in Proj

Every open neighborhood contains a positive homogeneous affine basic
neighborhood. This strengthens the unrestricted basic-open basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u v
namespace FLT.Mazur.GradedProjPositiveBasis
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A Proj point lies in a positive homogeneous basic open. -/
lemma exists_positive_basicOpen (x : Proj 𝒜) :
    ∃ (n : ℕ) (a : A), 0 < n ∧ a ∈ 𝒜 n ∧ x ∈ Proj.basicOpen 𝒜 a := by
  by_contra! h
  apply x.not_irrelevant_le
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro n hn a ha
  exact not_not.mp (h n a hn ha)

/-- Every open neighborhood contains a positive homogeneous affine basic neighborhood. -/
lemma exists_basicOpen_le {U : (Proj 𝒜).Opens} {x : Proj 𝒜} (hx : x ∈ U) :
    ∃ (n : ℕ) (a : A), 0 < n ∧ a ∈ 𝒜 n ∧ x ∈ Proj.basicOpen 𝒜 a ∧
      Proj.basicOpen 𝒜 a ≤ U := by
  obtain ⟨_, ⟨a, rfl⟩, ha, hU⟩ := Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen 𝒜) hx
  rw [Proj.basicOpen_eq_iSup_proj] at ha
  obtain ⟨n, hn⟩ := Opens.mem_iSup.mp ha
  obtain ⟨m, b, hm, hb, hxb⟩ := exists_positive_basicOpen 𝒜 x
  refine ⟨n + m, GradedRing.proj 𝒜 n a * b, Nat.add_pos_right n hm,
    SetLike.mul_mem_graded (show GradedRing.proj 𝒜 n a ∈ 𝒜 n from
      (DirectSum.decompose 𝒜 a n).property) hb, ?_, ?_⟩
  · rw [Proj.basicOpen_mul]
    exact ⟨hn, hxb⟩
  · rw [Proj.basicOpen_mul]
    apply inf_le_left.trans
    apply le_trans _ hU
    exact (le_iSup (fun j ↦ Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 j a)) n).trans_eq
      (Proj.basicOpen_eq_iSup_proj 𝒜 a).symm

end FLT.Mazur.GradedProjPositiveBasis
