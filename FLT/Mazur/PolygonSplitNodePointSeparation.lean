/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitNodeCoordinateValues
public import FLT.Mazur.PolygonCanonicalChartSpectrum
public import FLT.Mazur.PolygonCubicTorusPointSeparation

/-!
# Standard projective charts separate the split nodes

The evaluated chart ring map presents the actual image of each specified
node. Linear coordinates vanish there, and node coordinates detect its index.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodePresentation
open PolygonCubicSections ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (z : Spec (.of K))

/-- Evaluation of the actual canonical chart map at the split node. -/
def nodeChartRingMap : chartRing K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{0} n) →+* K :=
  (nodeEvaluation K n hn p q h a hn₂ i z).comp (chartAlgMap K n hn p q h a hn₂ i z).toRingHom

/-- The evaluated ring map gives the actual cubic image of the specified node. -/
lemma nodeChartRingMap_spec :
    Spec.map (CommRingCat.ofHom (nodeChartRingMap K n hn p q h a hn₂ i z)) ≫
      chartMap K _ (canonicalIndex.{0} n) =
        (nodeι K n i ≫ q).left ≫ cubicProjectiveMorphism K n hn p q h a := by
  have he := EvaluatedPrincipalRefinement.evaluation_chart
    (splitChart K n hn p q h hn₂ i) aEval.toRingHom
    (splitDenominator K n hn p q h a hn₂ i z)
    (nodeEvaluation K n hn p q h a hn₂ i z) (nodeEvaluation_comp K n hn p q h a hn₂ i z)
  change _ = aOrigin K ≫ splitChart K n hn p q h hn₂ i at he
  rw [splitChart_origin] at he
  change Spec.map (CommRingCat.ofHom (chartAlgMap K n hn p q h a hn₂ i z).toRingHom ≫
    CommRingCat.ofHom (nodeEvaluation K n hn p q h a hn₂ i z)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom (nodeEvaluation K n hn p q h a hn₂ i z)) ≫
    (Spec.map (CommRingCat.ofHom (affineCanonicalChartRingMap K n hn p q h a _ _)) ≫
      chartMap K _ (canonicalIndex.{0} n)) = _
  rw [affineCanonicalChartRingMap_spec, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ cubicProjectiveMorphism K n hn p q h a)
    (show Spec.map (CommRingCat.ofHom (nodeEvaluation K n hn p q h a hn₂ i z)) ≫
      splitDenominatorChart K n hn p q h a hn₂ i z = (nodeι K n i ≫ q).left from he)

include hn₂ in
/-- No split node image lies in a branch-linear coordinate chart. -/
lemma node_image_not_mem_linear (l : Fin n) :
    cubicProjectiveMorphism K n hn p q h a ((nodeι K n i ≫ q).left z) ∉
      chart K _ (interpolationIndex n l 1) := by
  change ((nodeι K n i ≫ q).left ≫ cubicProjectiveMorphism K n hn p q h a) z ∉ _
  rw [← nodeChartRingMap_spec K n hn p q h a hn₂ i z]
  change (Spec.map (CommRingCat.ofHom (nodeChartRingMap K n hn p q h a hn₂ i z)) ≫
    chartMap K _ (canonicalIndex.{0} n)) z ∉ _
  rw [field_chartMap_mem_iff]
  change ¬ nodeEvaluation K n hn p q h a hn₂ i z (coordinate K n hn p q h a hn₂ i z l 1) ≠ 0
  rw [nodeEvaluation_linear]
  simp

include hn₂ in
/-- A node-value coordinate chart contains exactly the node with that index. -/
lemma node_image_mem_node_iff (l : Fin n) :
    cubicProjectiveMorphism K n hn p q h a ((nodeι K n i ≫ q).left z) ∈
      chart K _ (interpolationIndex n l 0) ↔ i = l := by
  change ((nodeι K n i ≫ q).left ≫ cubicProjectiveMorphism K n hn p q h a) z ∈ _ ↔ _
  rw [← nodeChartRingMap_spec K n hn p q h a hn₂ i z]
  change (Spec.map (CommRingCat.ofHom (nodeChartRingMap K n hn p q h a hn₂ i z)) ≫
    chartMap K _ (canonicalIndex.{0} n)) z ∈ _ ↔ _
  rw [field_chartMap_mem_iff]
  exact nodeEvaluation_node_ne_zero_iff K n hn p q h a hn₂ i z l

end FLT.Mazur.PolygonSplitCubicCoordinates
