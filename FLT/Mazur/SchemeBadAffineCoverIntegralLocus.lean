/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverEquations
public import FLT.Mazur.OriginalPrimeIntegralLocus
public import FLT.Mazur.AffineValuationIntegralLift

/-!
# Constructed equation neighborhoods for the entire actual bad atlas

Local integrality on the finite bad atlas constructs exact original equations
and one common principal neighborhood. All valuation squares centered there
extend on their same bad charts. No whole-fiber completeness is assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood OriginalPrimeIntegralFiber AffineValuationGeneratorLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)
  (g : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType g]
attribute [local irreducible] badChartGenerators
local notation "G" => badChartGenerators s O g

/-- Simultaneous local integrality constructs exact equations for every fixed chart generator. -/
theorem exists_badChart_equations_of_local_integral (P : PrimeSpectrum R)
    (h : ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral) :
    ∃ p : ∀ i : (badCover O).I₀, G i → Polynomial R,
      (∀ (i : (badCover O).I₀) (b : G i), (p i b).eval₂ (badChartScalar s O i) b.val = 0) ∧
        badChartLeadingProduct s O g p ∉ P.asIdeal := by
  classical
  have hex (i : (badCover O).I₀) :=
    exists_finite_equations (badChartScalar s O i) (G i) P.asIdeal (h i)
  choose p hp using hex
  refine ⟨p, fun i ↦ (hp i).1, ?_⟩
  intro hm
  obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
  exact (hp i).2 hi

attribute [local irreducible] localizedMap badChartScalar badChartLeadingProduct

include g in
/-- One original scalar spreads integrality over every chart simultaneously. -/
theorem exists_principal_badChart_integral_neighborhood (P : PrimeSpectrum R)
    (h : ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum R, r ∉ Q.asIdeal →
      ∀ i, (localizedMap (badChartScalar s O i) Q.asIdeal).IsIntegral := by
  classical
  have hex (i : (badCover O).I₀) := exists_principal_integral_neighborhood
    (badChartScalar s O i) (G i) (badChartGenerators_generate s O g i) P (h i)
  choose r hr using hex
  refine ⟨∏ i, r i, ?_, fun Q hQ i ↦ (hr i).2 Q ?_⟩
  · intro hm
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact (hr i).1 hi
  · intro hm
    exact hQ (Ideal.IsPrime.prod_mem_iff.mpr ⟨i, Finset.mem_univ i, hm⟩)

include g in
/-- The simultaneous integrality locus is open in the unchanged original scalar spectrum. -/
theorem isOpen_badChart_integral_locus :
    IsOpen {P : PrimeSpectrum R |
      ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral} := by
  apply isOpen_iff_mem_nhds.mpr
  intro P hP
  obtain ⟨r, hr, h⟩ := exists_principal_badChart_integral_neighborhood s O g P hP
  exact Filter.mem_of_superset ((PrimeSpectrum.basicOpen r).isOpen.mem_nhds hr) h

include g in
/-- Every valuation centered in this constructed neighborhood extends on its original bad chart. -/
theorem exists_principal_badChart_lift_neighborhood (P : PrimeSpectrum R)
    (h : ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∀ (i : (badCover O).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i))),
      r ∉ (S.i₂ (IsLocalRing.closedPoint S.R)).asIdeal → S.commSq.HasLift := by
  obtain ⟨r, hr, hh⟩ := exists_principal_badChart_integral_neighborhood s O g P h
  exact ⟨r, hr, fun i S hS ↦ hasLift_of_localized_integral _ S (hh _ hS i)⟩

end FLT.Mazur.SchemeBadAffineCover
