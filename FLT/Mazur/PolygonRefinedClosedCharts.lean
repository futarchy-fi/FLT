/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitRefinementCover
public import FLT.Mazur.PolygonOneGonRefinementCover
public import FLT.Mazur.PolygonCanonicalChartSpectrum
public import FLT.Mazur.RefinedChartSpectrum
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closed affine factorizations of the refined cubic node charts

The surjective refined maps define closed immersions into explicit target
opens. Their composites into projective space are exactly the global cubic
morphism restricted to the retained-node source opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonCubicSections
open GeneratorDenominatorLocalization PrincipalAffineRefinement RefinedChartSpectrum
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (z : Spec (.of K))
local notation "s" => splitDenominator K n hn p q h a hn₂ i z
local notation "f" => chartAlgMap K n hn p q h a hn₂ i z
local notation "t" => sourceCoordinate K n i 0

/-- The exact closed affine factorization agrees with the cubic map on the refined source. -/
theorem exists_closed_chart :
    ∃ (b : Localization.Away t)
      (hb : map f t b = algebraMap (PolygonNodeEqualizer.A (R := K))
        (Localization.Away (f t)) s),
      IsClosedImmersion (morphism s f t b hb) ∧
      morphism s f t b hb ≫ inclusion b ≫ inclusion t ≫
        ProjectiveSpace.chartMap K _ (canonicalIndex.{0} n) =
      refinementChart K n hn p q h a hn₂ i z ≫ cubicProjectiveMorphism K n hn p q h a := by
  obtain ⟨b, hb, hsurj⟩ := exists_surjective_refinement K n hn p q h a hn₂ i z
  refine ⟨b, hb, RefinedChartSpectrum.isClosedImmersion s f t b hb hsurj, ?_⟩
  rw [morphism_inclusions_assoc]
  have he := affineCanonicalChartRingMap_spec K n hn p q h a
    (splitDenominatorChart K n hn p q h a hn₂ i z)
    (splitDenominatorChart_range_subset K n hn p q h a hn₂ i z)
  change Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ _ = _ at he
  rw [he]
  rfl

/-- The restricted cubic morphism is an immersion on each retained split-node open. -/
lemma refinement_isImmersion :
    IsImmersion (refinementChart K n hn p q h a hn₂ i z ≫
      cubicProjectiveMorphism K n hn p q h a) := by
  obtain ⟨b, hb, hc, he⟩ := exists_closed_chart K n hn p q h a hn₂ i z
  have := hc
  rw [← he]
  infer_instance

end PolygonSplitCubicCoordinates
namespace PolygonOneGonCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonCubicSections
open GeneratorDenominatorLocalization PrincipalAffineRefinement RefinedChartSpectrum
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (z : Spec (.of K)) (i : Fin 1)
local notation "s" => oneDenominator K hn p q h a z
local notation "f" => chartAlgMap K hn p q h a z
local notation "t" => sourceDenominator K a i

/-- The one-gon closed affine factorization has the same global projective composite. -/
theorem exists_closed_chart :
    ∃ (b : Localization.Away t)
      (hb : map f t b = algebraMap (PolygonNodePresentation.B (R := K))
        (Localization.Away (f t)) s),
      IsClosedImmersion (morphism s f t b hb) ∧
      morphism s f t b hb ≫ inclusion b ≫ inclusion t ≫
        ProjectiveSpace.chartMap K _ (canonicalIndex.{0} 1) =
      refinementChart K hn p q h a z i ≫ cubicProjectiveMorphism K 1 hn p q h a := by
  obtain ⟨b, hb, hsurj⟩ := exists_surjective_refinement K hn p q h a z i
  refine ⟨b, hb, RefinedChartSpectrum.isClosedImmersion s f t b hb hsurj, ?_⟩
  rw [morphism_inclusions_assoc]
  have he := affineCanonicalChartRingMap_spec K 1 hn p q h a
    (oneDenominatorChart K hn p q h a z)
    (oneDenominatorChart_range_subset K hn p q h a z)
  change Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ _ = _ at he
  rw [he]
  rfl

/-- The cubic morphism is an immersion on the retained one-gon node open. -/
lemma refinement_isImmersion :
    IsImmersion (refinementChart K hn p q h a z i ≫
      cubicProjectiveMorphism K 1 hn p q h a) := by
  obtain ⟨b, hb, hc, he⟩ := exists_closed_chart K hn p q h a z i
  have := hc
  rw [← he]
  infer_instance

end FLT.Mazur.PolygonOneGonCubicCoordinates
