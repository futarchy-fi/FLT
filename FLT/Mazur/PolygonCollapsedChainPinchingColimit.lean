/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainPinchingDiagram

/-!
# The full closed chain is the intrinsic pinching pushout

Arbitrary-target component descent proves the universal property of the actual
omitted-component and interior-node coproduct cocone.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainPinchingColimit
open PolygonCollapsedChainModel PolygonCollapsedChainPinchingDiagram
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n) {Y : Scheme}
  (f : components K n i ⟶ Y) (q : nodes K n i ⟶ Y)
  (w : toComponents K n i ≫ f = toNodes K n i ≫ q)

/-- The complete omitted component map in an arbitrary cocone. -/
def inputComponent (j : Fin n) (hj : j ≠ i) : ProjectiveLine.scheme K ⟶ Y :=
  componentι K n i ⟨j, hj⟩ ≫ f

include w in
/-- Each first endpoint recovers the cocone's interior node map. -/
theorem zero_input (j : NodeIndex n i) :
    ProjectiveLine.zero K ≫ inputComponent K n i f j.val j.property.1 =
      nodeι K n i j ≫ q := by
  have hw := congrArg (fun t ↦ branchι K n i j false ≫ t) w
  rw [branch_zero_assoc, branch_node_assoc] at hw
  exact hw

include w in
/-- Each successor infinity endpoint recovers the same interior node map. -/
theorem infinity_input (j : NodeIndex n i) :
    ProjectiveLine.infinity K ≫ inputComponent K n i f (finRotate n j.val) j.property.2 =
      nodeι K n i j ≫ q := by
  have hw := congrArg (fun t ↦ branchι K n i j true ≫ t) w
  rw [branch_infinity_assoc, branch_node_assoc] at hw
  exact hw

include w in
/-- The input cocone supplies exactly the required interior endpoint compatibility. -/
theorem input_condition (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    ProjectiveLine.zero K ≫ inputComponent K n i f j hj =
      ProjectiveLine.infinity K ≫ inputComponent K n i f (finRotate n j) hs :=
  (zero_input K n i f q w ⟨j, hj, hs⟩).trans (infinity_input K n i f q w ⟨j, hj, hs⟩).symm

/-- Descent of an arbitrary cocone on the specified intrinsic pinching diagram. -/
def desc : chain K n h i ⟶ Y :=
  PolygonCollapsedChainGlobalDescent.desc K n h i (inputComponent K n i f)
    (input_condition K n i f q w)

@[reassoc] theorem normalization_desc : normalization K n h i ≫ desc K n h i f q w = f := by
  apply Sigma.hom_ext
  intro j
  change componentι K n i j ≫ _ = componentι K n i j ≫ f
  rw [componentι_normalization_assoc]
  exact PolygonCollapsedChainComponentDescent.component_desc K n h i _ _ j.val j.property

@[reassoc] theorem nodeMap_desc : nodeMap K n h i ≫ desc K n h i f q w = q := by
  apply Sigma.hom_ext
  intro j
  change nodeι K n i j ≫ _ = nodeι K n i j ≫ q
  rw [nodeι_nodeMap_assoc]
  change ProjectiveLine.zero K ≫ component K n h i j.property.1 ≫
    PolygonCollapsedChainGlobalDescent.desc K n h i _ _ = _
  rw [PolygonCollapsedChainComponentDescent.component_desc]
  exact zero_input K n i f q w j

/-- The omitted-component and interior-node cocone is a genuine pushout in schemes. -/
theorem isPushout : IsPushout (toComponents K n i) (toNodes K n i)
    (normalization K n h i) (nodeMap K n h i) := by
  refine ⟨⟨condition K n h i⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ desc K n h i s.inl s.inr s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    exact normalization_desc K n h i s.inl s.inr s.condition
  · intro s
    exact nodeMap_desc K n h i s.inl s.inr s.condition
  · intro s m hm _
    apply PolygonCollapsedChainOpenCover.hom_ext K n h i
    intro j hj
    have he := congrArg (fun t ↦ componentι K n i ⟨j, hj⟩ ≫ t)
      (hm.trans (normalization_desc K n h i s.inl s.inr s.condition).symm)
    simpa only [componentι_normalization_assoc] using he

end FLT.Mazur.PolygonCollapsedChainPinchingColimit
