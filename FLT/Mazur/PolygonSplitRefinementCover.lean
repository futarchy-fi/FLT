/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitRefinementValue
public import FLT.Mazur.EvaluatedPrincipalRefinement

/-!
# Coverage by the split refinements used for surjectivity

The additional localization is exactly the one in the surjective ring map.
Its unit node value retains each specified node; together with the tori these
refinements cover the entire polygon, including the two-gon.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodePresentation
open PolygonCubicSections
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (z : Spec (.of K))

local notation "s" => splitDenominator K n hn p q h a hn₂ i z
local notation "f" => chartAlgMap K n hn p q h a hn₂ i z
local notation "t" => sourceCoordinate K n i 0

/-- The actual twice-localized source chart used by the surjective refinement. -/
def refinementChart : Spec (.of (Localization.Away (f t))) ⟶ C.left :=
  PrincipalAffineRefinement.chart (splitDenominatorChart K n hn p q h a hn₂ i z) (f t)

instance refinementChart_isOpenImmersion :
    IsOpenImmersion (refinementChart K n hn p q h a hn₂ i z) := by
  unfold refinementChart
  infer_instance

/-- The localized evaluation agrees with the original common-origin evaluation. -/
lemma nodeEvaluation_comp :
    (nodeEvaluation K n hn p q h a hn₂ i z).comp
      (algebraMap (A (R := K)) (Localization.Away s)) = aEval.toRingHom := by
  ext b
  change NodeDenominatorEqualizer.evaluation (first s) 0
    (splitDenominator_value_isUnit K n hn p q h a hn₂ i z)
    (LocalizationJointRestriction.restriction first.toRingHom s
      (algebraMap (A (R := K)) (Localization.Away s) b)) = (first b).eval 0
  rw [LocalizationJointRestriction.restriction_algebraMap]
  exact NodeDenominatorEqualizer.evaluation_algebraMap _ _ _ _

/-- The exact specified node survives the extra localization at the cubic coordinate. -/
lemma refinementChart_node_mem :
    (nodeι K n i ≫ q).left z ∈ Set.range (refinementChart K n hn p q h a hn₂ i z) := by
  have he := EvaluatedPrincipalRefinement.evaluation_chart
    (splitChart K n hn p q h hn₂ i) aEval.toRingHom s
    (nodeEvaluation K n hn p q h a hn₂ i z) (nodeEvaluation_comp K n hn p q h a hn₂ i z)
  change _ = aOrigin K ≫ splitChart K n hn p q h hn₂ i at he
  rw [splitChart_origin] at he
  have hm := EvaluatedPrincipalRefinement.mem_range
    (splitDenominatorChart K n hn p q h a hn₂ i z)
    (nodeEvaluation K n hn p q h a hn₂ i z) (f t)
    (nodeEvaluation_refinement_isUnit K n hn p q h a hn₂ i z) z
  change _ ∈ Set.range (refinementChart K n hn p q h a hn₂ i z) at hm
  rw [show Spec.map (CommRingCat.ofHom (nodeEvaluation K n hn p q h a hn₂ i z)) ≫
    splitDenominatorChart K n hn p q h a hn₂ i z = (nodeι K n i ≫ q).left from he] at hm
  exact hm

/-- These exact twice-localized sources and the torus opens cover the polygon. -/
lemma refinement_covers (v : C.left) :
    (∃ j, v ∈ torusOpen K n hn p q h j) ∨
      ∃ j x, v ∈ Set.range (refinementChart K n hn p q h a hn₂ j x) := by
  let := polygon_lfp K n hn p q h
  by_cases hv : v ∈ C.hom.smoothLocus
  · change v ∈ (C.hom.smoothLocus : Set C.left) at hv
    rw [smooth_range K n hn p q h] at hv
    exact Or.inl (Set.mem_iUnion.mp hv)
  · obtain ⟨j, x, rfl⟩ := (PolygonNodeLocus.nonsmooth_iff K n hn p q h v).mp hv
    exact Or.inr ⟨j, x, refinementChart_node_mem K n hn p q h a hn₂ j x⟩

end FLT.Mazur.PolygonSplitCubicCoordinates
