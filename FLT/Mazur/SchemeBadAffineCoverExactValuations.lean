/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverComponents
public import FLT.Mazur.AffineExactCenterValuationObstruction

/-!
# Exact-center valuation tests for the actual bad atlas

The finite domain components construct poles on the unchanged bad charts.
The scalar center is the selected original prime, not merely a generization.
Regularity at that exact center recovers original equations and a neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood OriginalPrimeIntegralFiber AffineValuationGeneratorLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)
  (g : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType g]
attribute [local irreducible] badChartGenerators

/-- A failed chart has a pole of a fixed original generator at the exact selected scalar prime. -/
theorem badChart_exact_center_obstruction (P : PrimeSpectrum R) (i : (badCover O).I₀)
    (h : ¬ (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral) :
    ∃ S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)),
      S.i₂ (closedPoint S.R) = P ∧ ∃ b ∈ badChartGenerators s O g i,
        genericCoordinates (badChartScalar s O i) S b ∉ (algebraMap S.R S.K).range :=
  exists_generator_square_of_not_integral _ P (badChart_minimalPrimes_finite O g i)
    (badChartGenerators s O g i : Set Γ((badCover O).X i, ⊤))
    (badChartGenerators_generate s O g i) h

/-- Full local integrality of an actual bad chart is exactly fixed-generator regularity. -/
theorem badChart_integral_iff_exact_center_regular (P : PrimeSpectrum R)
    (i : (badCover O).I₀) :
    (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral ↔
      ∀ S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)),
        S.i₂ (closedPoint S.R) = P → ∀ b ∈ badChartGenerators s O g i,
          genericCoordinates (badChartScalar s O i) S b ∈ (algebraMap S.R S.K).range := by
  refine ⟨fun hi S hc b _ ↦ ?_, fun hr ↦ ?_⟩
  · apply coordinates_mem_of_localized_integral
    rwa [hc]
  · exact localizedMap_integral_of_centered_generator_regular _ P
      (badChart_minimalPrimes_finite O g i) _ (badChartGenerators_generate s O g i) hr

include g in
/-- Full chart integrality is equivalently the existence of lifts at the exact original center. -/
theorem badChart_integral_iff_exact_center_lifts (P : PrimeSpectrum R)
    (i : (badCover O).I₀) :
    (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral ↔
      ∀ S : ValuativeCommSq (scalarMorphism (badChartScalar s O i)),
        S.i₂ (closedPoint S.R) = P → S.commSq.HasLift :=
  localizedMap_integral_iff_centered_lifts _ P (badChart_minimalPrimes_finite O g i)

/-- Exact-center regularity reconstructs exact original equations and their avoiding product. -/
theorem badCharts_equations_of_exact_center_regular (P : PrimeSpectrum R)
    (hr : ∀ (i : (badCover O).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i))),
      S.i₂ (closedPoint S.R) = P → ∀ b ∈ badChartGenerators s O g i,
        genericCoordinates (badChartScalar s O i) S b ∈ (algebraMap S.R S.K).range) :
    ∃ p : ∀ i : (badCover O).I₀, badChartGenerators s O g i → Polynomial R,
      (∀ (i : (badCover O).I₀) (b : badChartGenerators s O g i),
        (p i b).eval₂ (badChartScalar s O i) b.val = 0) ∧
          badChartLeadingProduct s O g p ∉ P.asIdeal :=
  exists_badChart_equations_of_local_integral s O g P
    (fun i ↦ (badChart_integral_iff_exact_center_regular s O g P i).mpr (hr i))

/-- Testing one exact center constructs lifts throughout a common original principal open. -/
theorem badCharts_lift_neighborhood_of_exact_center_regular (P : PrimeSpectrum R)
    (hr : ∀ (i : (badCover O).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i))),
      S.i₂ (closedPoint S.R) = P → ∀ b ∈ badChartGenerators s O g i,
        genericCoordinates (badChartScalar s O i) S b ∈ (algebraMap S.R S.K).range) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∀ (i : (badCover O).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar s O i))),
      r ∉ (S.i₂ (closedPoint S.R)).asIdeal → S.commSq.HasLift :=
  exists_principal_badChart_lift_neighborhood s O g P
    (fun i ↦ (badChart_integral_iff_exact_center_regular s O g P i).mpr (hr i))

end FLT.Mazur.SchemeBadAffineCover
