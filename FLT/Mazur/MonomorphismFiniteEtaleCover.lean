/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismFiniteEtaleInverse
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finitely many finite etale certificates for a complete kernel subset

Compactness selects finitely many actual affine coefficient neighborhoods.
Their finite etale covers carry original relation arrows. The neighborhoods
cover the prescribed entire subset; no one branch replaces the kernel.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.MonomorphismOpenImage
set_option backward.isDefEq.respectTransparency false
variable {D K : Scheme.{u}} (m : D ⟶ K) [Mono m]

/-- Compact subsets of the inverse region have a finite family of finite etale certificates. -/
theorem exists_finite_etale_image_cover (C : Set K) (hC : IsCompact C)
    (hCm : C ⊆ locus m) (U : K.Opens) (hCU : C ⊆ U) :
    ∃ (ι : Type u) (_ : Finite ι) (Z W : ι → Scheme.{u})
      (b : ∀ i, W i ⟶ K) (t : ∀ i, Z i ⟶ W i) (a : ∀ i, Z i ⟶ D),
      (∀ i, IsAffine (Z i) ∧ IsAffine (W i) ∧ Etale (b i) ∧ Etale (t i) ∧
        IsFinite (t i) ∧ Surjective (t i) ∧ a i ≫ m = t i ≫ b i ∧
        Set.range (b i) ⊆ U ∧ Set.range (b i) ⊆ locus m) ∧
      ∀ x ∈ C, ∃ i, x ∈ Set.range (b i) := by
  classical
  choose Z W b t a z hZ hW hb ht hf hs he hz hU using
    fun x : C ↦ exists_finite_etale_certificate m x.val (hCm x.property) U (hCU x.property)
  have hcover : C ⊆ ⋃ i : C, Set.range (b i) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, t ⟨x, hx⟩ (z ⟨x, hx⟩), hz ⟨x, hx⟩⟩
  obtain ⟨s, hsub⟩ := hC.elim_finite_subcover (fun i : C ↦ Set.range (b i))
    (fun i ↦ by let _ := hb i; exact (b i).isOpenMap.isOpen_range) hcover
  refine ⟨s, inferInstance, (fun i ↦ Z i.val), (fun i ↦ W i.val),
    (fun i ↦ b i.val), (fun i ↦ t i.val), (fun i ↦ a i.val), ?_, ?_⟩
  · intro i
    let _ := hb i.val
    let _ := ht i.val
    let _ := hs i.val
    exact ⟨hZ i.val, hW i.val, hb i.val, ht i.val, hf i.val, hs i.val, he i.val,
      hU i.val, etale_image_le_of_finite_cover m (b i.val) (t i.val) (a i.val) (he i.val)⟩
  · intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hsub hx)
    exact ⟨⟨i, hi⟩, hx⟩

end FLT.Mazur.MonomorphismOpenImage
