/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryIndependentIntegralTests

/-!
# A sealed integral branch criterion for large geometric applications

Seal the local integrality proposition so that geometric specializations
need not export its expanded tensor/localization type repeatedly. Its exact
equivalence is public; this predicate asserts integrality of a full principal
chart, and does not assert rank matching or scalar nilpotence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate boundaryFlatTestScalar
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (S : Type) [CommRing S] [Algebra T S]

/-- Local integrality of the full tensor principal chart at the specified branch prime. -/
@[irreducible] def boundaryIntegralFlatTest (Q : PrimeSpectrum S) (t : B) : Prop :=
  (localizedMap (boundaryFlatTestScalar s κ S t) Q.asIdeal).IsIntegral

/-- The sealed proposition retains precisely the full local-integrality obligation. -/
theorem boundaryIntegralFlatTest_iff (Q : PrimeSpectrum S) (t : B) :
    boundaryIntegralFlatTest s κ S Q t ↔
      (localizedMap (boundaryFlatTestScalar s κ S t) Q.asIdeal).IsIntegral := by
  rw [boundaryIntegralFlatTest]

/-- The sealed criterion constructs original coverage from exact fiber geometry. -/
theorem boundaryScalar_mem_of_integral_criterion [Module.Flat T S]
    (a : Finset B) (Q : PrimeSpectrum S)
    (hi : ∀ t ∈ a, boundaryIntegralFlatTest s κ S Q t)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z =
      PrimeSpectrum.comap (algebraMap T S) Q →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    PrimeSpectrum.comap (algebraMap T S) Q ∈ boundaryScalarNilpotenceOpen s κ a :=
  boundaryScalar_mem_of_integral_flat_tests s κ S a Q
    (fun t ht ↦ (boundaryIntegralFlatTest_iff s κ S Q t).mp (hi t ht)) hf

/-- Faithful flatness constructs the point while the criterion keeps its local integrality. -/
theorem boundaryScalar_mem_of_faithful_integral_criterion [Module.FaithfullyFlat T S]
    (a : Finset B) (P : PrimeSpectrum T)
    (hi : ∀ Q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap T S) Q = P →
      ∀ t ∈ a, boundaryIntegralFlatTest s κ S Q t)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    P ∈ boundaryScalarNilpotenceOpen s κ a :=
  boundaryScalar_mem_of_faithfully_flat_integral_tests s κ S a P
    (fun Q hQ t ht ↦ (boundaryIntegralFlatTest_iff s κ S Q t).mp (hi Q hQ t ht)) hf

omit S [CommRing S] [Algebra T S] in
/-- Independent full principal-chart criteria cover the same unchanged scalar prime. -/
theorem boundaryScalar_mem_of_independent_integral_criterion (a : Finset B)
    (Ss : a → Type) [∀ t, CommRing (Ss t)] [∀ t, Algebra T (Ss t)]
    [∀ t, Module.Flat T (Ss t)] (P : PrimeSpectrum T) (Qs : ∀ t, PrimeSpectrum (Ss t))
    (hQ : ∀ t, PrimeSpectrum.comap (algebraMap T (Ss t)) (Qs t) = P)
    (hi : ∀ t, boundaryIntegralFlatTest s κ (Ss t) (Qs t) t.val)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    P ∈ boundaryScalarNilpotenceOpen s κ a :=
  boundaryScalar_mem_of_independent_integral_tests s κ a Ss P Qs hQ
    (fun t ↦ (boundaryIntegralFlatTest_iff s κ (Ss t) (Qs t) t.val).mp (hi t)) hf

end FLT.Mazur.AffineScalarBoundaryNilpotence
