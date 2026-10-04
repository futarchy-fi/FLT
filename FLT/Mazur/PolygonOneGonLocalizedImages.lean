/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonGeneratorIdentities
public import FLT.Mazur.PolygonNodeChartScalars
public import FLT.Mazur.ExactSourceDenominatorLift
public import FLT.Mazur.NodeDenominatorGeneration

/-!
# Localized generator images for the actual one-gon chart

The common quadratic denominator is an explicit projective-ring element.
After compatible localization its two conductor numerators recover u and v.
The exact original source denominator then has a lift giving a surjective map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonOneGonCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodePresentation
open PolygonCubicSections PolygonPowerNodeEndpoints OneGonCubicElimination
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K)) (i : Fin 1)

/-- The actual B_s chart map, with the standard K-algebra structures. -/
def chartAlgMap : ProjectiveSpace.chartRing K _ (canonicalIndex.{u} 1) →ₐ[K]
    Localization.Away (oneDenominator K hn p q h a x) :=
  affineCanonicalChartAlgHom K 1 hn p q h a _
    (oneDenominatorChart_range_subset K hn p q h a x)
    (oneDenominatorChart_toBase K hn p q h a x)

/-- An interpolation coordinate in the original projective chart ring. -/
def sourceCoordinate (k : Fin 3) : ProjectiveSpace.chartRing K _ (canonicalIndex.{u} 1) :=
  ProjectiveSpace.coordinate K _ (canonicalIndex.{u} 1)
    ((cubicCoordinateEquiv.{u} 1).symm (.inr ⟨(i, k)⟩))

/-- The common denominator lifted explicitly to the actual projective chart ring. -/
def sourceDenominator : ProjectiveSpace.chartRing K _ (canonicalIndex.{u} 1) :=
  denominator (algebraMap K _ (weight K 1 a 3 i))
    (sourceCoordinate K i 0) (sourceCoordinate K i 1) (sourceCoordinate K i 2)

local notation "s" => oneDenominator K hn p q h a x
local notation "f" => chartAlgMap K hn p q h a x
local notation "t" => sourceDenominator K a i
local notation "F" => GeneratorDenominatorLocalization.map f t
local notation "c" => coordinate K hn p q h a x i
local notation "w" => algebraMap K (Localization.Away s) (weight K 1 a 3 i)

/-- Each source coordinate restricts to the already computed actual ratio. -/
lemma map_sourceCoordinate (k : Fin 3) : f (sourceCoordinate K i k) = c k := rfl

/-- The chosen target denominator maps to precisely the proved quadratic expression. -/
lemma map_sourceDenominator : f t = denominator w (c 0) (c 1) (c 2) := by
  simp only [sourceDenominator, denominator, map_neg, map_pow, map_mul, map_add,
    map_sub, map_ofNat, map_one, AlgHom.commutes, map_sourceCoordinate]

/-- The conductor has an explicit image after compatible localization. -/
lemma conductor_mem : algebraMap (B (R := K)) (Localization.Away (f t)) u ∈ (F).range := by
  rw [IsScalarTower.algebraMap_apply (B (R := K)) (Localization.Away s)
    (Localization.Away (f t))]
  apply GeneratorDenominatorLocalization.generator_mem f t
    (conductorNumerator (algebraMap K _ (weight K 1 a 3 i))
      (sourceCoordinate K i 0) (sourceCoordinate K i 1) (sourceCoordinate K i 2))
  rw [map_sourceDenominator]
  simpa only [conductorNumerator, map_neg, map_pow, map_mul, map_add,
    map_sub, map_one, AlgHom.commutes, map_sourceCoordinate] using
      (generator_identities K hn p q h a x i).1

/-- The first conductor monomial also lies in the same localized image. -/
lemma monomial_mem : algebraMap (B (R := K)) (Localization.Away (f t)) v ∈ (F).range := by
  rw [IsScalarTower.algebraMap_apply (B (R := K)) (Localization.Away s)
    (Localization.Away (f t))]
  apply GeneratorDenominatorLocalization.generator_mem f t
    (monomialNumerator (algebraMap K _ (weight K 1 a 3 i))
      (sourceCoordinate K i 0) (sourceCoordinate K i 1) (sourceCoordinate K i 2))
  rw [map_sourceDenominator]
  simpa only [monomialNumerator, map_neg, map_pow, map_mul, map_add,
    map_one, AlgHom.commutes, map_sourceCoordinate] using
      (generator_identities K hn p q h a x i).2

/-- A lift of the exact original source denominator completes ring surjectivity. -/
theorem exists_surjective_refinement :
    ∃ (b : Localization.Away t)
      (hb : F b = algebraMap (B (R := K)) (Localization.Away (f t)) s),
      Function.Surjective (ExactSourceDenominatorLift.refinedMap s (f t) F b hb) := by
  apply ExactSourceDenominatorLift.exists_surjective_refinement s (f t) F {u, v}
    NodeDenominatorGeneration.one_adjoin
  · intro g hg
    rcases hg with rfl | hg
    · exact conductor_mem K hn p q h a x i
    · rcases hg with rfl
      exact monomial_mem K hn p q h a x i
  · exact GeneratorDenominatorLocalization.inverse_mem f t

end FLT.Mazur.PolygonOneGonCubicCoordinates
