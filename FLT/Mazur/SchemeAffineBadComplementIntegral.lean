/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBadComplementCoordinates

/-!
# Original denominators from integral bad-complement quotients

Only the quotient coordinates of the bad complement must be integral over
the original scalar ring. The affine target itself may be nonintegral.
Whole-fiber containment then constructs a denominator in any chosen defining
ideal, preserving the exact nonreduced bad complement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (J : Ideal Γ(X, ⊤))

/-- Integrality in explicit quotient coordinates transfers to the constructed bad scheme. -/
theorem affineClosedComplementMap_scalar_isIntegral
    (hs : ((Ideal.Quotient.mk J).comp s).IsIntegral) :
    ((affineClosedComplementMap J).appTop.hom.comp s).IsIntegral := by
  let e := (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⧸ J))).commRingCatIsoToRingEquiv
  have he : e.toRingHom.comp ((affineClosedComplementMap J).appTop.hom.comp s) =
      (Ideal.Quotient.mk J).comp s := by
    ext r
    exact congrArg (fun f : Γ(X, ⊤) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ J) ↦ f (s r))
      (affineClosedComplementMap_coordinates J)
  intro x
  apply RingHom.IsIntegralElem.of_map e.injective
  change (e.toRingHom.comp ((affineClosedComplementMap J).appTop.hom.comp s)).IsIntegralElem _
  rw [he]
  exact hs (e x)

variable (O : X.Opens)
  (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ)

include hJ in
/-- Whole-fiber containment implies the actual constructed bad cover has empty original fiber. -/
theorem affineClosedComplement_empty_scalarFiber (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∀ b : affineClosedComplement J,
      scalarMorphism ((affineClosedComplementMap J).appTop.hom.comp s) b ≠ P := by
  intro b hb
  have hx : affineClosedComplementMap J b ∉ O := by
    have hr := affineClosedComplementMap_covers O J hJ
    have hb : affineClosedComplementMap J b ∈ Set.range (affineClosedComplementMap J) :=
      Set.mem_range_self b
    rw [hr] at hb
    exact hb
  apply hx
  apply hP
  rw [scalarMorphism_comp] at hb
  exact hb

include hJ in
/-- Quotient-only integrality and whole original fiber containment construct a safe scalar. -/
theorem mem_scalarNeighborhoodLocus_of_badQuotient_integral
    (hs : ((Ideal.Quotient.mk J).comp s).IsIntegral) (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    P ∈ scalarNeighborhoodLocus s O := by
  exact (scalarNeighborhoodLocus_badCover_iff s O (affineClosedComplementMap J)
    (affineClosedComplementMap_covers O J hJ)
    (scalarMorphism_isClosedMap _ (affineClosedComplementMap_scalar_isIntegral s J hs)) P).mpr
      (affineClosedComplement_empty_scalarFiber s J O hJ P hP)

include hJ in
/-- The denominator vanishes on the full chosen thickening, not just its closed points. -/
theorem exists_scalar_of_badQuotient_integral
    (hs : ((Ideal.Quotient.mk J).comp s).IsIntegral) (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ s r ∈ J ∧ X.basicOpen (s r) ≤ O :=
  exists_scalar_mem_affineBad s J O hJ P
    (mem_scalarNeighborhoodLocus_of_badQuotient_integral s J O hJ hs P hP)

/-- Every affine target uses its canonical quotient; no separate cover data are required. -/
theorem exists_scalar_of_affineBad_integral
    (hs : ((Ideal.Quotient.mk (affineBadIdeal O)).comp s).IsIntegral) (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O := by
  obtain ⟨r, hr, _, hO⟩ := exists_scalar_of_badQuotient_integral s (affineBadIdeal O) O
    (zeroLocus_affineBadIdeal O) hs P hP
  exact ⟨r, hr, hO⟩

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
