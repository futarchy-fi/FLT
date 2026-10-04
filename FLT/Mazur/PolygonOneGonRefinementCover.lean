/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonRefinementValue
public import FLT.Mazur.EvaluatedPrincipalRefinement

/-!
# Coverage by the one-gon refinements used for surjectivity

The additional localization is exactly the one in the surjective ring map.
Its unit node value retains each specified node; together with the tori these
refinements cover the entire polygon, including its self-pinched node.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonOneGonCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodePresentation
open PolygonCubicSections
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (z : Spec (.of K)) (i : Fin 1)

local notation "s" => oneDenominator K hn p q h a z
local notation "f" => chartAlgMap K hn p q h a z
local notation "t" => sourceDenominator K a i

/-- The actual twice-localized source chart used by the surjective refinement. -/
def refinementChart : Spec (.of (Localization.Away (f t))) ⟶ C.left :=
  PrincipalAffineRefinement.chart (oneDenominatorChart K hn p q h a z) (f t)

instance refinementChart_isOpenImmersion :
    IsOpenImmersion (refinementChart K hn p q h a z i) := by
  unfold refinementChart
  infer_instance

/-- The localized evaluation agrees with the identified-endpoint evaluation. -/
lemma nodeEvaluation_comp :
    (nodeEvaluation K hn p q h a z).comp
      (algebraMap (B (R := K)) (Localization.Away s)) = bEval.toRingHom := by
  ext b
  change NodeDenominatorEqualizer.evaluation (s).val 0
    (oneDenominator_value_isUnit K hn p q h a z)
    (LocalizationJointRestriction.restriction (B (R := K)).val.toRingHom s
      (algebraMap (B (R := K)) (Localization.Away s) b)) = b.val.eval 0
  rw [LocalizationJointRestriction.restriction_algebraMap]
  exact NodeDenominatorEqualizer.evaluation_algebraMap _ _ _ _

/-- The exact specified node survives the extra localization at the cubic coordinate. -/
lemma refinementChart_node_mem :
    (nodeι K 1 i ≫ q).left z ∈ Set.range (refinementChart K hn p q h a z i) := by
  have he := EvaluatedPrincipalRefinement.evaluation_chart
    (oneChart K hn p q h) bEval.toRingHom s
    (nodeEvaluation K hn p q h a z) (nodeEvaluation_comp K hn p q h a z)
  change _ = bOrigin K ≫ oneChart K hn p q h at he
  rw [oneChart_origin K hn p q h i] at he
  have hm := EvaluatedPrincipalRefinement.mem_range
    (oneDenominatorChart K hn p q h a z)
    (nodeEvaluation K hn p q h a z) (f t)
    (nodeEvaluation_refinement_isUnit K hn p q h a z i) z
  change _ ∈ Set.range (refinementChart K hn p q h a z i) at hm
  rw [show Spec.map (CommRingCat.ofHom (nodeEvaluation K hn p q h a z)) ≫
    oneDenominatorChart K hn p q h a z = (nodeι K 1 i ≫ q).left from he] at hm
  exact hm

/-- These exact twice-localized sources and the torus opens cover the polygon. -/
lemma refinement_covers (v : C.left) :
    (∃ j, v ∈ torusOpen K 1 hn p q h j) ∨
      ∃ j x, v ∈ Set.range (refinementChart K hn p q h a x j) := by
  let := polygon_lfp K 1 hn p q h
  by_cases hv : v ∈ C.hom.smoothLocus
  · change v ∈ (C.hom.smoothLocus : Set C.left) at hv
    rw [smooth_range K 1 hn p q h] at hv
    exact Or.inl (Set.mem_iUnion.mp hv)
  · obtain ⟨j, x, rfl⟩ := (PolygonNodeLocus.nonsmooth_iff K 1 hn p q h v).mp hv
    exact Or.inr ⟨j, x, refinementChart_node_mem K hn p q h a x j⟩

end FLT.Mazur.PolygonOneGonCubicCoordinates
