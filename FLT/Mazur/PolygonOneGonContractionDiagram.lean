/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonAtlas

/-!
# A pinching diagram contracting all but one polygon component

The target is the actual standard one-gon. The retained projective line maps
by its normalization, all other complete lines map to its node, and every
original node maps to that same target node. Both branches agree exactly.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The retained normalization map into the original standard one-gon. -/
def retainedComponent : component K ⟶ PolygonAtlas.polygon K 1 :=
  componentι K 1 0 ≫ PolygonAtlas.normalization K 1

/-- The original node of the standard one-gon. -/
def targetNode : point K ⟶ PolygonAtlas.polygon K 1 :=
  nodeι K 1 0 ≫ PolygonAtlas.nodes K 1

/-- Collapse an entire original projective component to the coefficient point. -/
def componentToPoint : component K ⟶ point K :=
  Over.homMk (ProjectiveLine.toBase K) (by simp)

/-- The zero branch of the retained component is the actual target node. -/
@[reassoc] theorem zero_retainedComponent :
    ProjectiveLine.zeroSection K ≫ retainedComponent K = targetNode K := by
  have hh := congrArg (fun f ↦ branchι K 1 0 false ≫ f)
    (PolygonAtlas.cocone K 1 (by decide))
  simpa only [branchι_toComponents_zero_assoc, branchι_toNodes_assoc,
    retainedComponent, targetNode, Category.assoc] using hh

/-- The infinity branch of the retained component is the same actual node. -/
@[reassoc] theorem infinity_retainedComponent :
    ProjectiveLine.infinitySection K ≫ retainedComponent K = targetNode K := by
  have hh := congrArg (fun f ↦ branchι K 1 0 true ≫ f)
    (PolygonAtlas.cocone K 1 (by decide))
  simpa only [branchι_toComponents_infinity_assoc, branchι_toNodes_assoc, next_one,
    retainedComponent, targetNode, Category.assoc] using hh

/-- Collapsing a complete component sends its zero endpoint to the coefficient point. -/
@[reassoc] theorem zero_componentToPoint :
    ProjectiveLine.zeroSection K ≫ componentToPoint K = 𝟙 (point K) := by
  apply Over.OverMorphism.ext
  exact (ProjectiveLine.zeroSection K).w

/-- Collapsing a complete component also sends its infinity endpoint to that point. -/
@[reassoc] theorem infinity_componentToPoint :
    ProjectiveLine.infinitySection K ≫ componentToPoint K = 𝟙 (point K) := by
  apply Over.OverMorphism.ext
  exact (ProjectiveLine.infinitySection K).w

variable (n : ℕ) (i : Fin n)

/-- Retain the selected original component and collapse all other complete components. -/
def normalizationMap : components K n ⟶ PolygonAtlas.polygon K 1 :=
  Sigma.desc fun j ↦ if j = i then retainedComponent K
    else componentToPoint K ≫ targetNode K

/-- Every original pinching node maps to the actual one-gon node. -/
def nodesMap : nodes K n ⟶ PolygonAtlas.polygon K 1 :=
  Sigma.desc fun _ ↦ targetNode K

/-- The normalization map retains the specified componentwise formula. -/
@[reassoc] theorem component_normalizationMap (j : Fin n) :
    componentι K n j ≫ normalizationMap K n i =
      if j = i then retainedComponent K else componentToPoint K ≫ targetNode K := by
  simp [componentι, normalizationMap]

/-- Each original node has the same target with its coefficient map unchanged. -/
@[reassoc] theorem node_nodesMap (j : Fin n) :
    nodeι K n j ≫ nodesMap K n = targetNode K := by
  simp [nodeι, nodesMap]

/-- Both original branches agree, including at the two ends of the retained component. -/
theorem cocone (hn : 0 < n) :
    toComponents K n hn ≫ normalizationMap K n i = toNodes K n ≫ nodesMap K n := by
  apply Sigma.hom_ext
  rintro ⟨j, b⟩
  change branchι K n j b ≫ _ = branchι K n j b ≫ _
  cases b
  · rw [branchι_toComponents_zero_assoc, branchι_toNodes_assoc,
      component_normalizationMap, node_nodesMap]
    split_ifs
    · exact zero_retainedComponent K
    · rw [zero_componentToPoint_assoc]
  · rw [branchι_toComponents_infinity_assoc, branchι_toNodes_assoc,
      component_normalizationMap, node_nodesMap]
    split_ifs
    · exact infinity_retainedComponent K
    · rw [infinity_componentToPoint_assoc]

end FLT.Mazur.PolygonOneGonContraction
