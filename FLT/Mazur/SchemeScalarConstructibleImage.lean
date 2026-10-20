/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarResidueImage
public import FLT.Mazur.SchemeScalarIntegralBadCover
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Constructible scalar images of compact nonaffine sources

A finite affine subcover reduces the actual scalar image to finitely many
finite-presentation ring-map images. The source need not itself be affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
variable {R : Type} [CommRing R] {X : Scheme} (s : R →+* Γ(X, ⊤))

/-- The actual scalar image is the union of the images on any open cover. -/
theorem scalar_image_eq_cover_union (U : X.OpenCover) :
    Set.range (scalarMorphism s) =
      ⋃ i, Set.range (scalarMorphism ((U.f i).appTop.hom.comp s)) := by
  ext P
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, y, rfl⟩ := U.exists_eq x
    exact ⟨i, y, by rw [scalarMorphism_comp]; rfl⟩
  · rintro ⟨i, y, rfl⟩
    exact ⟨U.f i y, by rw [scalarMorphism_comp]; rfl⟩

/-- A finite affine cover with finitely presented scalar maps has constructible image. -/
theorem scalar_image_constructible_of_finite_cover (U : X.OpenCover)
    [Finite U.I₀] [∀ i, IsAffine (U.X i)]
    (hs : ∀ i, ((U.f i).appTop.hom.comp s).FinitePresentation) :
    IsConstructible (Set.range (scalarMorphism s)) := by
  rw [scalar_image_eq_cover_union s U]
  apply IsConstructible.iUnion
  intro i
  rw [scalarMorphism_range_eq_comap]
  exact PrimeSpectrum.isConstructible_range_comap (hs i)

/-- Compactness extracts the finite affine cover needed for constructibility. -/
theorem scalar_image_constructible_of_affineCover [CompactSpace X]
    (hs : ∀ i, ((X.affineCover.f i).appTop.hom.comp s).FinitePresentation) :
    IsConstructible (Set.range (scalarMorphism s)) := by
  apply scalar_image_constructible_of_finite_cover s X.affineCover.finiteSubcover
  intro i
  exact hs _

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
