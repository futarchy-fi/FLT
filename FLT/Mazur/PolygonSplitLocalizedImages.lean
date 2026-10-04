/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitGeneratorIdentities
public import FLT.Mazur.PolygonNodeChartScalars
public import FLT.Mazur.ExactSourceDenominatorLift

/-!
# Generator images and exact denominator lifts for split charts

Localize the actual projective chart and source compatibly at the node-value
coordinate. Both branch generators are then in the image. Lifting the original
chosen denominator gives a further target localization with a surjective map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodeLocalization
open PolygonNodePresentation PolygonCubicSections PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (z : Spec (.of K))

/-- The actual split chart map with its proved algebra compatibility. -/
def chartAlgMap : ProjectiveSpace.chartRing K _ (canonicalIndex.{u} n) →ₐ[K]
    Localization.Away (splitDenominator K n hn p q h a hn₂ i z) :=
  affineCanonicalChartAlgHom K n hn p q h a _
    (splitDenominatorChart_range_subset K n hn p q h a hn₂ i z)
    (splitDenominatorChart_toBase K n hn p q h a hn₂ i z)

/-- A projective interpolation coordinate before restriction to the node. -/
def sourceCoordinate (l : Fin n) (k : Fin 3) :
    ProjectiveSpace.chartRing K _ (canonicalIndex.{u} n) :=
  ProjectiveSpace.coordinate K _ (canonicalIndex.{u} n)
    ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(l, k)⟩))

local notation "s" => splitDenominator K n hn p q h a hn₂ i z
local notation "f" => chartAlgMap K n hn p q h a hn₂ i z
local notation "t" => sourceCoordinate K n i 0
local notation "F" => GeneratorDenominatorLocalization.map f t

/-- On the compatible localization, the first generator has its explicit image witness. -/
lemma first_mem : algebraMap (A (R := K)) (Localization.Away (f t)) x ∈ (F).range := by
  rw [IsScalarTower.algebraMap_apply (A (R := K)) (Localization.Away s)
    (Localization.Away (f t))]
  exact GeneratorDenominatorLocalization.generator_mem f t (sourceCoordinate K n i 1) _
    (first_generator K n hn p q h a hn₂ i z)

/-- The second generator uses the matching-weight multiple of the successor quadratic. -/
lemma second_mem : algebraMap (A (R := K)) (Localization.Away (f t)) y ∈ (F).range := by
  rw [IsScalarTower.algebraMap_apply (A (R := K)) (Localization.Away s)
    (Localization.Away (f t))]
  apply GeneratorDenominatorLocalization.generator_mem f t
    (algebraMap K _ (weight K n a 3 (finRotate n i)) *
      sourceCoordinate K n (finRotate n i) 2)
  rw [map_mul, AlgHom.commutes]
  exact second_generator K n hn p q h a hn₂ i z

/-- The chosen source denominator lifts after these compatible localizations. -/
theorem exists_surjective_refinement :
    ∃ (b : Localization.Away t)
      (hb : F b = algebraMap (A (R := K)) (Localization.Away (f t)) s),
      Function.Surjective (ExactSourceDenominatorLift.refinedMap s (f t) F b hb) := by
  apply ExactSourceDenominatorLift.exists_surjective_refinement s (f t) F {x, y} a_adjoin
  · intro g hg
    rcases hg with rfl | hg
    · exact first_mem K n hn p q h a hn₂ i z
    · rcases hg with rfl
      exact second_mem K n hn p q h a hn₂ i z
  · exact GeneratorDenominatorLocalization.inverse_mem f t

end FLT.Mazur.PolygonSplitCubicCoordinates
