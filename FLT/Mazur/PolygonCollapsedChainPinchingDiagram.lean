/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainComponentDescent

/-!
# The intrinsic component and interior-node pinching diagram

Only omitted complete projective lines and nodes between them occur. The two
boundary endpoints remain unpinched, including for the single surviving line.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainPinchingDiagram
open PolygonCollapsedChainModel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

/-- The original complete components remaining after contraction. -/
abbrev ComponentIndex := {j : Fin n // j ≠ i}

/-- Exactly the original nodes joining two omitted components. -/
abbrev NodeIndex := {j : Fin n // j ≠ i ∧ finRotate n j ≠ i}

/-- The normalization coproduct of the intrinsic chain. -/
def components : Scheme := ∐ fun _ : ComponentIndex n i ↦ ProjectiveLine.scheme K

/-- The coefficient points at the interior nodes. -/
def nodes : Scheme := ∐ fun _ : NodeIndex n i ↦ Spec (.of K)

/-- Two endpoint points for each interior node. -/
def branches : Scheme := ∐ fun _ : NodeIndex n i × Bool ↦ Spec (.of K)

/-- The original complete normalization component injection. -/
def componentι (j : ComponentIndex n i) : ProjectiveLine.scheme K ⟶ components K n i :=
  Sigma.ι (fun _ : ComponentIndex n i ↦ ProjectiveLine.scheme K) j

/-- The original interior node injection. -/
def nodeι (j : NodeIndex n i) : Spec (.of K) ⟶ nodes K n i :=
  Sigma.ι (fun _ : NodeIndex n i ↦ Spec (.of K)) j

/-- The endpoint injection, false for zero and true for successor infinity. -/
def branchι (j : NodeIndex n i) (b : Bool) : Spec (.of K) ⟶ branches K n i :=
  Sigma.ι (fun _ : NodeIndex n i × Bool ↦ Spec (.of K)) (j, b)

/-- The two actual endpoints on adjacent omitted projective lines. -/
def toComponents : branches K n i ⟶ components K n i :=
  Sigma.desc fun jb ↦ match jb.2 with
    | false => ProjectiveLine.zero K ≫ componentι K n i ⟨jb.1.val, jb.1.property.1⟩
    | true => ProjectiveLine.infinity K ≫
        componentι K n i ⟨finRotate n jb.1.val, jb.1.property.2⟩

/-- Both endpoints are sent to their original interior node. -/
def toNodes : branches K n i ⟶ nodes K n i := Sigma.desc fun jb ↦ nodeι K n i jb.1

@[reassoc] theorem branch_zero (j : NodeIndex n i) :
    branchι K n i j false ≫ toComponents K n i =
      ProjectiveLine.zero K ≫ componentι K n i ⟨j.val, j.property.1⟩ :=
  by simp only [branchι, toComponents, Sigma.ι_comp_desc]

@[reassoc] theorem branch_infinity (j : NodeIndex n i) :
    branchι K n i j true ≫ toComponents K n i = ProjectiveLine.infinity K ≫
      componentι K n i ⟨finRotate n j.val, j.property.2⟩ :=
  by simp only [branchι, toComponents, Sigma.ι_comp_desc]

@[reassoc] theorem branch_node (j : NodeIndex n i) (b : Bool) :
    branchι K n i j b ≫ toNodes K n i = nodeι K n i j := by
  simp only [branchι, toNodes, Sigma.ι_comp_desc]

/-- The actual normalization map into the full closed chain. -/
def normalization : components K n i ⟶ chain K n h i :=
  Sigma.desc fun j ↦ component K n h i j.property

/-- The interior nodes retain their original zero endpoint images. -/
def nodeMap : nodes K n i ⟶ chain K n h i :=
  Sigma.desc fun j ↦ ProjectiveLine.zero K ≫ component K n h i j.property.1

@[reassoc] theorem componentι_normalization (j : ComponentIndex n i) :
    componentι K n i j ≫ normalization K n h i = component K n h i j.property :=
  by simp only [componentι, normalization, Sigma.ι_comp_desc]

@[reassoc] theorem nodeι_nodeMap (j : NodeIndex n i) :
    nodeι K n i j ≫ nodeMap K n h i =
      ProjectiveLine.zero K ≫ component K n h i j.property.1 := by
  simp only [nodeι, nodeMap, Sigma.ι_comp_desc]

/-- Both original endpoint maps have the same image in the full chain. -/
theorem condition : toComponents K n i ≫ normalization K n h i =
    toNodes K n i ≫ nodeMap K n h i := by
  apply Sigma.hom_ext
  rintro ⟨j, b⟩
  change branchι K n i j b ≫ _ = branchι K n i j b ≫ _
  cases b
  · rw [branch_zero_assoc, componentι_normalization, branch_node_assoc, nodeι_nodeMap]
  · rw [branch_infinity_assoc, componentι_normalization, branch_node_assoc, nodeι_nodeMap]
    exact (component_endpoints K n h i j.val j.property.1 j.property.2).symm

/-- The specified coproduct cocone, without any assumed universal property. -/
def cocone : PushoutCocone (toComponents K n i) (toNodes K n i) :=
  PushoutCocone.mk (normalization K n h i) (nodeMap K n h i) (condition K n h i)

end FLT.Mazur.PolygonCollapsedChainPinchingDiagram
