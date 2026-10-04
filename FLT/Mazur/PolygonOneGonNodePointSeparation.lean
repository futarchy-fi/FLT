/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonRefinementCover
public import FLT.Mazur.PolygonCanonicalChartSpectrum
public import FLT.Mazur.PolygonCubicTorusPointSeparation

/-!
# Standard projective charts separate the one-gon node

The evaluated chart ring map presents the actual image of each specified
node. Linear coordinates vanish there, and node coordinates detect its index.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonOneGonCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodePresentation
open PolygonCubicSections ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (i : Fin 1) (z : Spec (.of K))

/-- Evaluation of the actual canonical chart map at the one-gon node. -/
def nodeChartRingMap : chartRing K (Fin (1 * 3 + 1 + 1)) (canonicalIndex.{0} 1) →+* K :=
  (nodeEvaluation K hn p q h a z).comp (chartAlgMap K hn p q h a z).toRingHom

/-- The evaluated ring map gives the actual cubic image of the specified node. -/
lemma nodeChartRingMap_spec :
    Spec.map (CommRingCat.ofHom (nodeChartRingMap K hn p q h a z)) ≫
      chartMap K _ (canonicalIndex.{0} 1) =
        (nodeι K 1 i ≫ q).left ≫ cubicProjectiveMorphism K 1 hn p q h a := by
  have he := EvaluatedPrincipalRefinement.evaluation_chart
    (oneChart K hn p q h) bEval.toRingHom
    (oneDenominator K hn p q h a z)
    (nodeEvaluation K hn p q h a z) (nodeEvaluation_comp K hn p q h a z)
  change _ = bOrigin K ≫ oneChart K hn p q h at he
  rw [oneChart_origin K hn p q h i] at he
  change Spec.map (CommRingCat.ofHom (chartAlgMap K hn p q h a z).toRingHom ≫
    CommRingCat.ofHom (nodeEvaluation K hn p q h a z)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom (nodeEvaluation K hn p q h a z)) ≫
    (Spec.map (CommRingCat.ofHom (affineCanonicalChartRingMap K 1 hn p q h a _ _)) ≫
      chartMap K _ (canonicalIndex.{0} 1)) = _
  rw [affineCanonicalChartRingMap_spec, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ cubicProjectiveMorphism K 1 hn p q h a)
    (show Spec.map (CommRingCat.ofHom (nodeEvaluation K hn p q h a z)) ≫
      oneDenominatorChart K hn p q h a z = (nodeι K 1 i ≫ q).left from he)

/-- No one-gon node image lies in a branch-linear coordinate chart. -/
lemma node_image_not_mem_linear (l : Fin 1) :
    cubicProjectiveMorphism K 1 hn p q h a ((nodeι K 1 i ≫ q).left z) ∉
      chart K _ (interpolationIndex 1 l 1) := by
  change ((nodeι K 1 i ≫ q).left ≫ cubicProjectiveMorphism K 1 hn p q h a) z ∉ _
  rw [← nodeChartRingMap_spec K hn p q h a i z]
  change (Spec.map (CommRingCat.ofHom (nodeChartRingMap K hn p q h a z)) ≫
    chartMap K _ (canonicalIndex.{0} 1)) z ∉ _
  rw [field_chartMap_mem_iff]
  change ¬ nodeEvaluation K hn p q h a z (coordinate K hn p q h a z l 1) ≠ 0
  rw [(nodeEvaluation_coordinates K hn p q h a z l).2.1]
  simp


end FLT.Mazur.PolygonOneGonCubicCoordinates
