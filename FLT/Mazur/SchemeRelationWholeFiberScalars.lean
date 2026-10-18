/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeWholeFiberOpenComposition
public import FLT.Mazur.SchemeScalarAvoidanceCover
public import FLT.Mazur.SchemeAffineBadComplementLocalIntegral

/-!
# Original scalar avoidance for a constructed relation source open

The safe prime locus of the constructed source open is exactly the safe
prime locus of the relation open, using the same original scalar ring.
Consequently local integrality need only be proved for the bad quotient of
the relation; no closedness of either endpoint map is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeWholeFiberOpen
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X Z : Scheme}
  (s : R →+* Γ(X, ⊤)) (f : Z ⟶ X) (L : Z.Opens)

/-- Constructing the source open loses no safe primes over the original scalar ring. -/
theorem scalarNeighborhoodLocus_wholeFiber :
    scalarNeighborhoodLocus s (locus f L) =
      scalarNeighborhoodLocus (f.appTop.hom.comp s) L := by
  change locus (scalarMorphism s) (locus f L) =
    locus (scalarMorphism (f.appTop.hom.comp s)) L
  rw [← locus_comp, scalarMorphism_comp]

/-- Whole fibers over the original prime suffice when the composite bad image is closed. -/
theorem mem_scalarNeighborhoodLocus_wholeFiber_of_badImage_closed
    (P : PrimeSpectrum R)
    (hc : IsClosed ((f ≫ scalarMorphism s) '' (L : Set Z)ᶜ))
    (hP : ∀ z : Z, (f ≫ scalarMorphism s) z = P → z ∈ L) :
    P ∈ scalarNeighborhoodLocus s (locus f L) := by
  change P ∈ locus (scalarMorphism s) (locus f L)
  rw [← locus_comp]
  exact (mem_locus_iff_of_badImage_closed _ L hc P).mpr hP

/-- Local integrality of the relation's bad quotient constructs a safe source prime. -/
theorem mem_scalarNeighborhoodLocus_wholeFiber_of_badQuotient [IsAffine Z]
    (J : Ideal Γ(Z, ⊤))
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(Z, ⊤)) = Z.toSpecΓ '' (L : Set Z)ᶜ)
    (P : PrimeSpectrum R)
    (hInt : (OriginalPrimeIntegralFiber.localizedMap
      ((Ideal.Quotient.mk J).comp (f.appTop.hom.comp s)) P.asIdeal).IsIntegral)
    (hP : ∀ z : Z, scalarMorphism (f.appTop.hom.comp s) z = P → z ∈ L) :
    P ∈ scalarNeighborhoodLocus s (locus f L) := by
  rw [scalarNeighborhoodLocus_wholeFiber]
  exact mem_scalarNeighborhoodLocus_of_badQuotient_local_integral
    (f.appTop.hom.comp s) J L hJ P hInt hP

/-- The scalar obtained on the relation already defines a usable open on the source. -/
theorem exists_source_scalar_of_relation_neighborhood (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus (f.appTop.hom.comp s) L) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ locus f L := by
  apply (mem_scalarNeighborhoodLocus_iff s (locus f L) P).mp
  rwa [scalarNeighborhoodLocus_wholeFiber]

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
