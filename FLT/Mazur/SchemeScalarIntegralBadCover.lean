/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarIntegralCover

/-!
# Original denominators from integral covers of the bad complement

Only the unusable complement needs a closed image over the original scalar
ring. An integral affine scheme covering that complement supplies this
closedness; the usable target itself need not be integral or affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X B : Scheme}
  (s : R →+* Γ(X, ⊤)) (O : X.Opens) (j : B ⟶ X)
  (hj : Set.range j = (O : Set X)ᶜ)

include hj in
/-- An actual cover of the unusable complement computes its entire original scalar image. -/
theorem scalar_badImage_eq_badCover_range :
    scalarMorphism s '' (O : Set X)ᶜ =
      Set.range (scalarMorphism (j.appTop.hom.comp s)) := by
  rw [← hj, ← Set.range_comp, scalarMorphism_comp]
  rfl

include hj in
/-- Closedness is needed only on a cover of the bad complement. -/
theorem scalarNeighborhoodLocus_badCover_iff
    (hs : IsClosedMap (scalarMorphism (j.appTop.hom.comp s))) (P : PrimeSpectrum R) :
    P ∈ scalarNeighborhoodLocus s O ↔
      ∀ b : B, scalarMorphism (j.appTop.hom.comp s) b ≠ P := by
  change P ∉ closure (scalarMorphism s '' (O : Set X)ᶜ) ↔ _
  rw [scalar_badImage_eq_badCover_range s O j hj, hs.isClosed_range.closure_eq]
  exact not_exists

variable [IsAffine B]

/-- Affine scalar images have the same range as the induced map of prime spectra. -/
theorem scalarMorphism_range_eq_comap (t : R →+* Γ(B, ⊤)) :
    Set.range (scalarMorphism t) = Set.range (PrimeSpectrum.comap t) := by
  change Set.range ((PrimeSpectrum.comap t) ∘ B.toSpecΓ) = _
  exact B.toSpecΓ.homeomorph.surjective.range_comp _

include hj in
/-- The avoidance ideal is the radical of the original scalars killed on the full bad cover. -/
theorem scalarAvoidanceIdeal_eq_badCover_ker_radical :
    scalarAvoidanceIdeal s O = (RingHom.ker (j.appTop.hom.comp s)).radical := by
  unfold scalarAvoidanceIdeal
  rw [scalar_badImage_eq_badCover_range s O j hj, scalarMorphism_range_eq_comap,
    PrimeSpectrum.vanishingIdeal_range_comap]

include hj in
/-- At an original prime, the exact bad-cover kernel suffices; no integrality is required. -/
theorem mem_scalarNeighborhoodLocus_iff_badCover_ker (P : PrimeSpectrum R) :
    P ∈ scalarNeighborhoodLocus s O ↔ ¬ RingHom.ker (j.appTop.hom.comp s) ≤ P.asIdeal := by
  rw [mem_scalarNeighborhoodLocus_iff_not_le,
    scalarAvoidanceIdeal_eq_badCover_ker_radical s O j hj, P.isPrime.radical_le_iff]

include hj in
/-- A safe original prime supplies a denominator vanishing exactly on the unreduced bad cover. -/
theorem exists_scalar_killing_badCover (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus s O) :
    ∃ r : R, r ∉ P.asIdeal ∧ j.appTop (s r) = 0 ∧ X.basicOpen (s r) ≤ O := by
  have hk := (mem_scalarNeighborhoodLocus_iff_badCover_ker s O j hj P).mp hP
  obtain ⟨r, hr, hrP⟩ := IsConcreteLE.not_le_iff_exists.mp hk
  refine ⟨r, hrP, hr, (mem_scalarAvoidanceIdeal_iff s O r).mp ?_⟩
  rw [scalarAvoidanceIdeal_eq_badCover_ker_radical s O j hj]
  exact Ideal.le_radical hr

include hj in
/-- Integral bad-cover coordinates and an empty original fiber construct a denominator. -/
theorem exists_scalar_of_integral_badCover
    (hs : (j.appTop.hom.comp s).IsIntegral) (P : PrimeSpectrum R)
    (hP : ∀ b : B, scalarMorphism (j.appTop.hom.comp s) b ≠ P) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O :=
  (mem_scalarNeighborhoodLocus_iff s O P).mp
    ((scalarNeighborhoodLocus_badCover_iff s O j hj
      (scalarMorphism_isClosedMap _ hs) P).mpr hP)

include hj in
/-- The bad-cover fiber criterion proves noncontainment in the specified original prime. -/
theorem scalarAvoidanceIdeal_not_le_of_integral_badCover
    (hs : (j.appTop.hom.comp s).IsIntegral) (P : PrimeSpectrum R)
    (hP : ∀ b : B, scalarMorphism (j.appTop.hom.comp s) b ≠ P) :
    ¬ scalarAvoidanceIdeal s O ≤ P.asIdeal := by
  obtain ⟨r, hr, hO⟩ := exists_scalar_of_integral_badCover s O j hj hs P hP
  intro h
  exact hr (h ((mem_scalarAvoidanceIdeal_iff s O r).mpr hO))

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
