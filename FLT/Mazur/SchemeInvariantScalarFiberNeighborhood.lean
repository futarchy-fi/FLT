/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarPrincipalNeighborhoodFamily
public import FLT.Mazur.SchemeOriginalScalarOpenCorrections

/-!
# Original scalar neighborhoods from invariant-coordinate integrality

For a finite group, integrality of the target invariant ring over the original
scalar ring implies integrality of all target coordinates. Consequently a
whole scalar fiber contained in a stable image open supplies the original
principal neighborhood needed for fixed-target extension.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood SchemeCoordinateAction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X : Scheme} (ρ : G →* Aut X) (σ : R →+* invariantCoordinates ρ)

/-- Integral invariant scalars are integral in the full unreduced target coordinate ring. -/
theorem invariantScalarCoordinates_isIntegral (hσ : σ.IsIntegral) :
    (invariantScalarCoordinates ρ σ).IsIntegral := by
  let _ := coordinateAction ρ
  change ((FiniteGroupQuotient.inclusion G Γ(X, ⊤)).comp σ).IsIntegral
  exact RingHom.IsIntegral.trans σ _ hσ
    (FiniteGroupQuotient.inclusion_isIntegral G Γ(X, ⊤))

variable [IsAffine X]

/-- Integrality of the invariant scalar map proves closedness over the original scalar spectrum. -/
theorem invariantScalarMorphism_isClosedMap (hσ : σ.IsIntegral) :
    IsClosedMap (scalarMorphism (invariantScalarCoordinates ρ σ)) :=
  scalarMorphism_isClosedMap _ (invariantScalarCoordinates_isIntegral ρ σ hσ)

/-- A whole original fiber in the usable image domain supplies its original principal scalar. -/
theorem exists_originalScalar_of_invariantIntegral_fiber
    (hσ : σ.IsIntegral) (O : X.Opens) (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism (invariantScalarCoordinates ρ σ) x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (σ r).val ≤ O :=
  exists_scalar_of_closed_fiber _ O P (invariantScalarMorphism_isClosedMap ρ σ hσ) hP

/-- The original bad-image condition follows from integrality and whole-fiber containment. -/
theorem mem_scalarNeighborhoodLocus_of_invariantIntegral_fiber
    (hσ : σ.IsIntegral) (O : X.Opens) (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism (invariantScalarCoordinates ρ σ) x = P → x ∈ O) :
    P ∈ scalarNeighborhoodLocus (invariantScalarCoordinates ρ σ) O :=
  (mem_scalarNeighborhoodLocus_iff _ O P).mpr
    (exists_originalScalar_of_invariantIntegral_fiber ρ σ hσ O P hP)

end FLT.Mazur.SchemeFiniteGroupQuotient
