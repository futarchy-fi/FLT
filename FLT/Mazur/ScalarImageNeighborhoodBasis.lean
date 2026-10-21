/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageQuotient

/-!
# Original scalar neighborhoods of exact image points

Every neighborhood of a point of the exact image contains a principal
neighborhood defined by an original scalar outside the original prime.
An original prime in the image closure has a unique exact-image point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageQuotient
variable {R : Type} [CommRing R] {X : Scheme.{0}} (b : X ⟶ Spec (.of R))

/-- Every neighborhood in the exact quotient has an unchanged original scalar refinement. -/
theorem exists_original_principal (y : Spec (.of (Scalars b)))
    (U : (Spec (.of (Scalars b))).Opens) (hy : y ∈ U) :
    ∃ r : R, r ∉ (inclusion b y).asIdeal ∧
      PrimeSpectrum.basicOpen (quotient b r) ≤ U := by
  obtain ⟨_, ⟨s, rfl⟩, hys, hsU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen y hy
  obtain ⟨r, rfl⟩ := quotient_surjective b s
  exact ⟨r, hys, hsU⟩

/-- The exact image supplies a point above every original prime in the source-image closure. -/
theorem existsUnique_image_point [IsAffine X] (x : Spec (.of R))
    (hx : x ∈ closure (Set.range b)) :
    ∃! y : Spec (.of (Scalars b)), inclusion b y = x := by
  rw [← inclusion_range b] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy, fun z hz ↦ (inclusion b).isClosedEmbedding.injective (hz.trans hy.symm)⟩

/-- Original scalar refinement retains the specified original prime exactly. -/
theorem exists_original_principal_over (x : Spec (.of R)) (y : Spec (.of (Scalars b)))
    (hyx : inclusion b y = x) (U : (Spec (.of (Scalars b))).Opens) (hy : y ∈ U) :
    ∃ r : R, r ∉ x.asIdeal ∧ PrimeSpectrum.basicOpen (quotient b r) ≤ U := by
  obtain ⟨r, hr, hU⟩ := exists_original_principal b y U hy
  exact ⟨r, hyx ▸ hr, hU⟩

end FLT.Mazur.SchemeScalarImageQuotient
