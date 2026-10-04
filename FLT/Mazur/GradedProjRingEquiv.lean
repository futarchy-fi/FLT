/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Proj isomorphisms from degree-preserving ring equivalences

A ring equivalence preserving and reflecting the actual homogeneous pieces
induces an isomorphism of projective schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousIdeal
universe u
namespace FLT.Mazur.GradedProjRingEquiv
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (e : A ≃+* B) (he : ∀ n a, e a ∈ ℬ n ↔ a ∈ 𝒜 n)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A degree-preserving equivalence defines a graded ring map. -/
def forward : 𝒜 →+*ᵍ ℬ where
  __ := e.toRingHom
  map_mem := fun {n a} ha ↦ (he n a).mpr ha

/-- Degree reflection makes the inverse equivalence a graded ring map. -/
def backward : ℬ →+*ᵍ 𝒜 where
  __ := e.symm.toRingHom
  map_mem := fun {n b} hb ↦ (he n (e.symm b)).mp (by simpa using hb)

/-- Positive degrees are in the image of the irrelevant ideal under the equivalence. -/
lemma irrelevant_le_forward : ℬ₊ ≤ 𝒜₊.map (forward 𝒜 ℬ e he) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le ℬ).mpr
  intro n hn b hb
  have ha := (backward 𝒜 ℬ e he).map_mem hb
  have h := Ideal.mem_map_of_mem (forward 𝒜 ℬ e he).toRingHom
    (mem_irrelevant_of_mem 𝒜 hn ha)
  change e (e.symm b) ∈ (𝒜₊.map (forward 𝒜 ℬ e he)).toIdeal at h
  rw [e.apply_symm_apply] at h
  exact h

/-- Positive degrees are in the image of the irrelevant ideal under the inverse. -/
lemma irrelevant_le_backward : 𝒜₊ ≤ ℬ₊.map (backward 𝒜 ℬ e he) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le 𝒜).mpr
  intro n hn a ha
  have hb := (forward 𝒜 ℬ e he).map_mem ha
  have h := Ideal.mem_map_of_mem (backward 𝒜 ℬ e he).toRingHom
    (mem_irrelevant_of_mem ℬ hn hb)
  change e.symm (e a) ∈ (ℬ₊.map (backward 𝒜 ℬ e he)).toIdeal at h
  rw [e.symm_apply_apply] at h
  exact h

/-- A graded ring equivalence induces an actual isomorphism of Proj schemes. -/
def iso : Proj ℬ ≅ Proj 𝒜 where
  hom := Proj.map (forward 𝒜 ℬ e he) (irrelevant_le_forward 𝒜 ℬ e he)
  inv := Proj.map (backward 𝒜 ℬ e he) (irrelevant_le_backward 𝒜 ℬ e he)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (forward 𝒜 ℬ e he).comp (backward 𝒜 ℬ e he) = GradedRingHom.id ℬ := by
      ext b
      exact e.apply_symm_apply b
    simp only [h, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (backward 𝒜 ℬ e he).comp (forward 𝒜 ℬ e he) = GradedRingHom.id 𝒜 := by
      ext a
      exact e.symm_apply_apply a
    simp only [h, Proj.map_id]

/-- The induced isomorphism carries the expected standard basic opens. -/
lemma iso_preimage_basicOpen (a : A) :
    (iso 𝒜 ℬ e he).hom ⁻¹ᵁ Proj.basicOpen 𝒜 a = Proj.basicOpen ℬ (e a) := rfl

end FLT.Mazur.GradedProjRingEquiv
