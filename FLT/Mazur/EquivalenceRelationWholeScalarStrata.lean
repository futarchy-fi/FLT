/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteScalarFiber
public import FLT.Mazur.ScalarWholeFiberStrata

/-!
# The exact original scalar locus with complete nonempty full fibers

Remove the scalar image of every incomplete full invariant prime from the
actual scalar image. Finite presentation and the existing finite complete-locus
equations construct a finite scalar stratification of this exact locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient ScalarConstructibleStrata
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
attribute [local irreducible] source action restrictedAction
local notation "ρ" => restrictedAction (action e I o) B hB
variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))

/-- The actual scalar image after removing all incomplete full-character images. -/
@[irreducible] def wholeCompleteScalarLocus : Set (PrimeSpectrum R) :=
  Set.range (PrimeSpectrum.comap σ) \
    PrimeSpectrum.comap σ '' (completeAffineOrbitImage e I o B hB : Set (quotient ρ))ᶜ

/-- Membership asserts nonemptiness and completeness of every full invariant prime. -/
theorem mem_wholeCompleteScalarLocus_iff (P : PrimeSpectrum R) :
    P ∈ wholeCompleteScalarLocus e I o B hB σ ↔
      (∃ Q : quotient ρ, PrimeSpectrum.comap σ Q = P) ∧
        ∀ Q : quotient ρ, PrimeSpectrum.comap σ Q = P →
          Q ∈ completeAffineOrbitImage e I o B hB := by
  rw [wholeCompleteScalarLocus]
  exact (whole_fiber_iff_image_difference σ _ P).symm

/-- All full characters over a scalar point in the constructed locus are complete. -/
theorem wholeCompleteScalarLocus_full_prime (P : PrimeSpectrum R)
    (hP : P ∈ wholeCompleteScalarLocus e I o B hB σ)
    (Q : quotient ρ) (hQ : PrimeSpectrum.comap σ Q = P) :
    Q ∈ completeAffineOrbitImage e I o B hB :=
  ((mem_wholeCompleteScalarLocus_iff e I o B hB σ P).mp hP).2 Q hQ

/-- The whole-complete scalar locus has finitely many exact scalar equations and inequations. -/
theorem exists_wholeCompleteScalarLocus_strata [TopologicalSpace.NoetherianSpace B.toScheme]
    (hfp : σ.FinitePresentation) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      P ∈ wholeCompleteScalarLocus e I o B hB σ ↔
        ∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal := by
  obtain ⟨pieces, h⟩ := exists_whole_fiber_equation_strata σ hfp
    (completeAffineOrbitTests e I o B hB)
  refine ⟨pieces, fun P ↦ ?_⟩
  rw [mem_wholeCompleteScalarLocus_iff, h P]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro Q
  apply imp_congr_right
  intro _
  change Q ∈ (completeAffineOrbitImage e I o B hB : Set (quotient ρ)) ↔ _
  rw [← completeAffineOrbitTests_zeroLocus]
  rfl

end FLT.Mazur.EquivalenceRelationNormalizedFrames
