/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantSpectrum

/-!
# Invariant principal neighborhoods on an affine quotient

An open set stable under the group is saturated for the quotient map. Its
image is open and its points have principal neighborhoods cut out by invariant
functions. These are the actual principal charts used in quotient gluing.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  (U : Set (PrimeSpectrum A))
  (hU : ∀ (P Q : PrimeSpectrum A) (g : G), Q.asIdeal = g • P.asIdeal → P ∈ U → Q ∈ U)

include hU in
/-- An invariant set is saturated for the map to the fixed-ring spectrum. -/
theorem invariant_preimage_image :
    PrimeSpectrum.comap (inclusion G A) ⁻¹' (PrimeSpectrum.comap (inclusion G A) '' U) = U := by
  apply Set.Subset.antisymm
  · rintro Q ⟨P, hP, hPQ⟩
    obtain ⟨g, hg⟩ := (spectrum_eq_iff_orbit G A P Q).mp hPQ
    exact hU P Q g hg hP
  · exact Set.subset_preimage_image _ _

include hU in
/-- An invariant open descends to an open of the affine quotient. -/
theorem invariant_image_isOpen (ho : IsOpen U) :
    IsOpen (PrimeSpectrum.comap (inclusion G A) '' U) := by
  rw [← (spectrum_isQuotientMap G A).isOpen_preimage]
  rwa [invariant_preimage_image G A U hU]

include hU in
/-- Invariant functions supply a principal neighborhood basis inside invariant opens. -/
theorem exists_invariant_basicOpen (ho : IsOpen U) (P : PrimeSpectrum A) (hP : P ∈ U) :
    ∃ r : invariantRing G A,
      P ∈ PrimeSpectrum.basicOpen (r : A) ∧
        (PrimeSpectrum.basicOpen (r : A) : Set (PrimeSpectrum A)) ⊆ U := by
  obtain ⟨_, ⟨r, rfl⟩, hrP, hrU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
    (invariant_image_isOpen G A U hU ho) (PrimeSpectrum.comap (inclusion G A) P)
    ⟨P, hP, rfl⟩
  refine ⟨r, hrP, fun Q hQ ↦ ?_⟩
  have hQ' : Q ∈ PrimeSpectrum.comap (inclusion G A) ⁻¹'
      (PrimeSpectrum.comap (inclusion G A) '' U) := hrU hQ
  rwa [invariant_preimage_image G A U hU] at hQ'

end FLT.Mazur.FiniteGroupQuotient
