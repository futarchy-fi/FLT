/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStandardFieldExtension
public import FLT.Mazur.PolygonOneGonContractionBaseChange

/-!
# Contraction between chosen standard polygons after field extension

The actual standard-polygon comparisons carry the retained component, all
collapsed components, and every node to their original base-changed maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonContractionFieldExtension
open PolygonPinching PolygonFieldExtension PolygonStandardFieldExtension
open PolygonOneGonContraction ProjectiveLineFieldExtension
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K L : Type) [Field K] [Field L] [Algebra K L]
local notation "F" => Over.pullback (ProjectiveLineProductCharts.parameterToBase K L)

/-- The retained complete component becomes the chosen extended one-gon normalization. -/
@[reassoc] theorem retained_comparison :
    retainedComponent L ≫ (iso K L 1 (by decide)).hom =
      (componentIso K L).hom ≫ (F).map (retainedComponent K) := by
  rw [retainedComponent, Category.assoc, component_iso]
  rfl

/-- The actual target node is preserved by the chosen standard one-gon comparison. -/
@[reassoc] theorem targetNode_comparison :
    targetNode L ≫ (iso K L 1 (by decide)).hom =
      (pointIso K L).hom ≫ (F).map (targetNode K) := by
  rw [targetNode, Category.assoc, node_iso]
  rfl

/-- Collapse to the coefficient point is compatible with the specified field comparisons. -/
@[reassoc] theorem componentToPoint_comparison :
    componentToPoint L ≫ (pointIso K L).hom =
      (componentIso K L).hom ≫ (F).map (componentToPoint K) := by
  apply (cancel_mono (pointIso K L).inv).mp
  exact Over.mkIdTerminal.hom_ext _ _

variable (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n)

omit [NeZero n] in
/-- The entire normalization contraction diagram commutes under the standard comparisons. -/
@[reassoc] theorem normalizationMap_comparison :
    normalizationMap L n i ≫ (iso K L 1 (by decide)).hom =
      (componentsIso K L n).hom ≫ (F).map (normalizationMap K n i) := by
  apply Sigma.hom_ext
  intro j
  have hi : componentι L n j ≫ (componentsIso K L n).hom =
      (componentIso K L).hom ≫ (F).map (componentι K n j) :=
    inclusion K L (fun _ : Fin n ↦ component K) (fun _ ↦ component L) _ j
  change componentι L n j ≫ _ = componentι L n j ≫ _
  rw [component_normalizationMap_assoc, ← Category.assoc, hi, Category.assoc,
    ← Functor.map_comp, component_normalizationMap]
  by_cases hj : j = i
  · simp only [ite_eq_left hj]
    exact retained_comparison K L
  · simp only [ite_eq_right hj, Category.assoc, Functor.map_comp]
    rw [targetNode_comparison, componentToPoint_comparison_assoc]

omit [NeZero n] in
/-- The whole node contraction diagram also commutes with the chosen field comparisons. -/
@[reassoc] theorem nodesMap_comparison :
    nodesMap L n ≫ (iso K L 1 (by decide)).hom =
      (nodesIso K L n).hom ≫ (F).map (nodesMap K n) := by
  apply Sigma.hom_ext
  intro j
  have hi : nodeι L n j ≫ (nodesIso K L n).hom =
      (pointIso K L).hom ≫ (F).map (nodeι K n j) :=
    inclusion K L (fun _ : Fin n ↦ point K) (fun _ ↦ point L) _ j
  change nodeι L n j ≫ _ = nodeι L n j ≫ _
  rw [node_nodesMap_assoc, ← Category.assoc, hi, Category.assoc,
    ← Functor.map_comp, node_nodesMap, targetNode_comparison]

/-- Contraction of the chosen standard polygons agrees with actual pullback of contraction. -/
theorem contraction_comparison :
    contraction L n hn (PolygonAtlas.normalization L n) (PolygonAtlas.nodes L n)
        (PolygonAtlas.isPushout L n hn) i ≫ (iso K L 1 (by decide)).hom =
      (iso K L n hn).hom ≫ (F).map
        (contraction K n hn (PolygonAtlas.normalization K n) (PolygonAtlas.nodes K n)
          (PolygonAtlas.isPushout K n hn) i) := by
  apply (PolygonAtlas.isPushout L n hn).hom_ext
  · rw [normalization_contraction_assoc, normalization_iso_assoc, ← Functor.map_comp,
      normalization_contraction, normalizationMap_comparison]
  · rw [nodes_contraction_assoc, nodes_iso_assoc, ← Functor.map_comp,
      nodes_contraction, nodesMap_comparison]

/-- The chosen-standard contraction also agrees with descent on the pulled-back original span. -/
theorem baseChangedContraction_comparison :
    contraction L n hn (PolygonAtlas.normalization L n) (PolygonAtlas.nodes L n)
        (PolygonAtlas.isPushout L n hn) i ≫ (iso K L 1 (by decide)).hom =
      (iso K L n hn).hom ≫ baseChangedContraction K n hn
        (PolygonAtlas.normalization K n) (PolygonAtlas.nodes K n)
        (PolygonAtlas.isPushout K n hn) i (ProjectiveLineProductCharts.parameterToBase K L) := by
  rw [baseChangedContraction_eq]
  exact contraction_comparison K L n hn i

end FLT.Mazur.PolygonContractionFieldExtension
