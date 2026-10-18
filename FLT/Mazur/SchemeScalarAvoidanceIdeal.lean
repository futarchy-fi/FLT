/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarPrincipalNeighborhood

/-!
# The original ideal controlling principal image neighborhoods

The original scalars whose principal target is usable form the vanishing
ideal of the bad target image. This ideal is the contraction of the actual
target vanishing ideal, not an ideal in a substituted invariant scalar ring.
Its noncontainment in the specified original prime is the exact criterion
for the principal extension construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} (s : R →+* Γ(X, ⊤)) (O : X.Opens)

/-- The original ideal of scalars vanishing on the image of the unusable target complement. -/
def scalarAvoidanceIdeal : Ideal R :=
  PrimeSpectrum.vanishingIdeal (scalarMorphism s '' (O : Set X)ᶜ)

/-- Ideal membership is exactly containment of the original scalar's principal target. -/
theorem mem_scalarAvoidanceIdeal_iff (r : R) :
    r ∈ scalarAvoidanceIdeal s O ↔ X.basicOpen (s r) ≤ O := by
  rw [scalarAvoidanceIdeal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro hr x hx
    by_contra hxo
    have hx' : scalarMorphism s x ∈ PrimeSpectrum.basicOpen r := by
      change x ∈ scalarMorphism s ⁻¹ᵁ PrimeSpectrum.basicOpen r
      rwa [scalarMorphism_preimage]
    exact hx' (hr _ ⟨x, hxo, rfl⟩)
  · rintro hr y ⟨x, hx, rfl⟩
    by_contra hxr
    apply hx
    apply hr
    rw [← scalarMorphism_preimage]
    exact hxr

/-- The geometric avoidance locus is exactly the nonvanishing locus of the original ideal. -/
theorem mem_scalarNeighborhoodLocus_iff_not_le (P : PrimeSpectrum R) :
    P ∈ scalarNeighborhoodLocus s O ↔ ¬ scalarAvoidanceIdeal s O ≤ P.asIdeal := by
  change P ∉ closure (scalarMorphism s '' (O : Set X)ᶜ) ↔ _
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  rfl

/-- The ideal is computed by contraction from full target coordinates, including nilpotents. -/
theorem scalarAvoidanceIdeal_eq_comap :
    scalarAvoidanceIdeal s O =
      Ideal.comap s (PrimeSpectrum.vanishingIdeal (X.toSpecΓ '' (O : Set X)ᶜ)) := by
  ext r
  simp only [scalarAvoidanceIdeal, Ideal.mem_comap, PrimeSpectrum.mem_vanishingIdeal,
    Set.forall_mem_image]
  rfl

/-- This original ideal is radical even when the original rings are nonreduced. -/
theorem scalarAvoidanceIdeal_isRadical : (scalarAvoidanceIdeal s O).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- Enlarging the usable open enlarges the ideal of available original denominators. -/
theorem scalarAvoidanceIdeal_mono {V : X.Opens} (h : O ≤ V) :
    scalarAvoidanceIdeal s O ≤ scalarAvoidanceIdeal s V := by
  intro r hr
  exact (mem_scalarAvoidanceIdeal_iff s V r).mpr
    (((mem_scalarAvoidanceIdeal_iff s O r).mp hr).trans h)

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
