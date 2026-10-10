/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveFiniteAffineNeighborhood
public import FLT.Mazur.SectionGradedProjOfAmple

/-!
# Finite sets on schemes with an ample line bundle

Transport common affine neighborhoods through the canonical section-ring Proj
open immersion. The neighborhood can be chosen inside any prescribed open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AmpleFiniteNeighborhood

universe u

variable {X : Scheme.{u}}

/-- Open subschemes of Proj have a common affine neighborhood for every finite set. -/
theorem of_openImmersion {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (f : X ⟶ Proj 𝒜) [IsOpenImmersion f] (W : X.Opens) (s : Finset X)
    (hs : ∀ x ∈ s, x ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ (∀ x ∈ s, x ∈ V) ∧ V ≤ W := by
  classical
  obtain ⟨U, hU, hUs, hUW⟩ := ProjectiveFiniteNeighborhood.exists_affineOpen 𝒜
    (f ''ᵁ W) (s.image f) (by
      rintro y hy
      obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, hs x hxs, rfl⟩)
  refine ⟨f ⁻¹ᵁ U, hU.preimage_of_isOpenImmersion f ?_, ?_, ?_⟩
  · exact hUW.trans (by rintro y ⟨x, _, rfl⟩; exact ⟨x, rfl⟩)
  · intro x hx
    exact hUs _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · rw [← f.preimage_image_eq W]
    exact (TopologicalSpace.Opens.map f.base).monotone hUW

/-- Stacks 01ZY for the established ample-line-bundle predicate. -/
theorem of_ample (L : X.Modules) [Fact (FCurve.LocallyFreeRankOne L)]
    (hL : FCurve.AmpleLineBundle L) (W : X.Opens) (s : Finset X)
    (hs : ∀ x ∈ s, x ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ (∀ x ∈ s, x ∈ V) ∧ V ≤ W := by
  let h := SectionGradedProjConstruction.positivePowerGenerated_of_ample L hL
  let _ := SectionGradedProjOfAmple.isOpenImmersion L hL h
  exact of_openImmersion (SectionGradedSum.grade L ⊤)
    (SectionGradedProjConstruction.toProj L h) W s hs

end FLT.Mazur.AmpleFiniteNeighborhood
