/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Finite generization tests for images of closed Noetherian sets

The generic points of finitely many irreducible components give actual points
of the closed source set. Their images detect its entire image closure, even
when the map is not closed. This applies to excluded residual envelope loci.
-/

@[expose] public noncomputable section
open TopologicalSpace
namespace FLT.Mazur.NoetherianClosedImage
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [NoetherianSpace X] [QuasiSober X]

/-- Every closed Noetherian sober set is the closure of finitely many of its actual points. -/
theorem exists_finite_generics {Z : Set X} (hZ : IsClosed Z) :
    ∃ F : Set X, F.Finite ∧ F ⊆ Z ∧ closure F = Z := by
  classical
  obtain ⟨S, hS, hclosed, hirr, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  let _ := hS.fintype
  let g : S → X := fun s ↦ (hirr s.val s.property).genericPoint
  have hg (s : S) : IsGenericPoint (g s) s.val :=
    (hirr s.val s.property).isGenericPoint_genericPoint (hclosed s.val s.property)
  refine ⟨Set.range g, Set.finite_range g, ?_, ?_⟩
  · rintro x ⟨s, rfl⟩
    rw [hcover]
    exact Set.mem_sUnion.mpr ⟨s.val, s.property, (hg s).mem⟩
  · apply subset_antisymm
    · apply closure_minimal _ hZ
      rintro x ⟨s, rfl⟩
      rw [hcover]
      exact Set.mem_sUnion.mpr ⟨s.val, s.property, (hg s).mem⟩
    · intro x hx
      rw [hcover] at hx
      obtain ⟨s, hs, hx⟩ := Set.mem_sUnion.mp hx
      have hcl : x ∈ closure ({g ⟨s, hs⟩} : Set X) := ((hg ⟨s, hs⟩).specializes hx).mem_closure
      have hsub : ({g ⟨s, hs⟩} : Set X) ⊆ Set.range g :=
        Set.singleton_subset_iff.mpr ⟨⟨s, hs⟩, rfl⟩
      exact closure_mono hsub hcl

/-- Finite actual source points detect every accumulation point of the closed-set image. -/
theorem exists_finite_image_generizations (f : X → Y) (hf : Continuous f)
    {Z : Set X} (hZ : IsClosed Z) :
    ∃ F : Set X, F.Finite ∧ F ⊆ Z ∧
      ∀ y : Y, y ∈ closure (f '' Z) ↔ ∃ x ∈ F, f x ⤳ y := by
  obtain ⟨F, hF, hFZ, hcl⟩ := exists_finite_generics hZ
  refine ⟨F, hF, hFZ, fun y ↦ ?_⟩
  have he : f '' F = ⋃ x ∈ F, ({f x} : Set Y) := by ext; simp [eq_comm]
  rw [← hcl, closure_image_closure hf, he, hF.closure_biUnion]
  simp only [Set.mem_iUnion, exists_prop, specializes_iff_mem_closure]

/-- Accumulation is witnessed by an actual excluded source point over a generization. -/
theorem mem_closure_image_iff (f : X → Y) (hf : Continuous f)
    {Z : Set X} (hZ : IsClosed Z) (y : Y) :
    y ∈ closure (f '' Z) ↔ ∃ x ∈ Z, f x ⤳ y := by
  obtain ⟨F, _, hFZ, hF⟩ := exists_finite_image_generizations f hf hZ
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := (hF y).mp hy
    exact ⟨x, hFZ hx, hxy⟩
  · rintro ⟨x, hx, hxy⟩
    have hsub : ({f x} : Set Y) ⊆ f '' Z :=
      Set.singleton_subset_iff.mpr ⟨x, hx, rfl⟩
    exact closure_mono hsub hxy.mem_closure

end FLT.Mazur.NoetherianClosedImage
