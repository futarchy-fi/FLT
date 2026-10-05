/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalRefinementOpenImmersion

/-!
# Finite principal target refinements of affine open immersions

The image of an affine open immersion admits finitely many principal target
opens whose inverse images cover the source. Their defining elements are
actual target ring elements, so their covers can enter coefficient descent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- An affine open immersion has a finite principal target refinement, with
both the source cover and containment in the original image retained. -/
theorem exists_finite_principal_target_refinement {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    ∃ t : Finset R,
      (⨆ i : t, PrimeSpectrum.basicOpen (f i)) = ⊤ ∧
      ∀ r ∈ t, (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
        Set.range (Spec.map (CommRingCat.ofHom f)) := by
  classical
  let F := Spec.map (CommRingCat.ofHom f)
  have hex (x : PrimeSpectrum S) : ∃ r : R,
      x ∈ PrimeSpectrum.basicOpen (f r) ∧
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆ Set.range F := by
    obtain ⟨U, ⟨r, rfl⟩, hr, hU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show F x ∈ Set.range F from ⟨x, rfl⟩) F.isOpenEmbedding.isOpen_range
    exact ⟨r, hr, hU⟩
  choose z hz hsub using hex
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : PrimeSpectrum S ↦ (PrimeSpectrum.basicOpen (f (z x)) : Set (PrimeSpectrum S)))
    (fun _ ↦ (PrimeSpectrum.basicOpen _).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hz x⟩)
  refine ⟨s.image z, ?_, ?_⟩
  · apply top_le_iff.mp
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨z y, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩, hxy⟩
  · intro r hr
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hr
    exact hsub x

end FLT.Mazur.Approximation
