/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CyclicPinchingRotation
public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Reflection of the original cyclic pinching span

Reflection negates component indices and reverses each projective coordinate.
The node index is minus the original index minus one, and the two branches
are exchanged. These formulas include polygons with one or two components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {n : ℕ} [NeZero n]

/-- Reflection of the component index fixes the identity component. -/
def reflectIndex (i : Fin n) : Fin n :=
  (ZMod.finEquiv n).symm (-ZMod.finEquiv n i)

/-- The node between components i and i+1 goes to the node between -i-1 and -i. -/
def reflectNodeIndex (i : Fin n) : Fin n :=
  (ZMod.finEquiv n).symm (-ZMod.finEquiv n i - 1)

@[simp] theorem reflectIndex_reflectIndex (i : Fin n) :
    reflectIndex (reflectIndex i) = i := by simp [reflectIndex]

@[simp] theorem reflectNodeIndex_reflectNodeIndex (i : Fin n) :
    reflectNodeIndex (reflectNodeIndex i) = i := by
  simp [reflectNodeIndex, sub_eq_add_neg]

@[simp] theorem reflectIndex_zero : reflectIndex (0 : Fin n) = 0 := by
  apply (ZMod.finEquiv n).injective
  simp [reflectIndex]

/-- The original infinity branch becomes the reflected zero branch. -/
theorem reflectIndex_next (hn : 0 < n) (i : Fin n) :
    reflectIndex (next hn i) = reflectNodeIndex i := by
  apply (ZMod.finEquiv n).injective
  simp [reflectIndex, reflectNodeIndex, next_eq_add_one, sub_eq_add_neg, add_comm]

/-- The original zero branch becomes infinity on the reflected successor component. -/
theorem next_reflectNodeIndex (hn : 0 < n) (i : Fin n) :
    next hn (reflectNodeIndex i) = reflectIndex i := by
  apply (ZMod.finEquiv n).injective
  simp [reflectIndex, reflectNodeIndex, next_eq_add_one]

variable (K : Type u) [Field K]
local notation "r" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)

/-- Reflect every original projective component and reverse its two endpoints. -/
def componentsReflection : components K n ⟶ components K n :=
  Sigma.desc fun i => r ≫ componentι K n (reflectIndex i)

/-- Reflect each node and exchange its two ordered branches. -/
def branchesReflection : branches K n ⟶ branches K n :=
  Sigma.desc fun ib => branchι K n (reflectNodeIndex ib.1) (!ib.2)

/-- Reflect the node index without changing its coefficient point. -/
def nodesReflection : nodes K n ⟶ nodes K n :=
  Sigma.desc fun i => nodeι K n (reflectNodeIndex i)

@[reassoc (attr := simp)] theorem componentι_reflection (i : Fin n) :
    componentι K n i ≫ componentsReflection K = r ≫ componentι K n (reflectIndex i) := by
  simp [componentι, componentsReflection]

@[reassoc (attr := simp)] theorem branchι_reflection (i : Fin n) (b : Bool) :
    branchι K n i b ≫ branchesReflection K =
      branchι K n (reflectNodeIndex i) (!b) := by
  simp [branchι, branchesReflection]

@[reassoc (attr := simp)] theorem nodeι_reflection (i : Fin n) :
    nodeι K n i ≫ nodesReflection K = nodeι K n (reflectNodeIndex i) := by
  simp [nodeι, nodesReflection]

/-- Reflection respects the entire original normalization leg. -/
theorem reflection_toComponents (hn : 0 < n) :
    branchesReflection K ≫ toComponents K n hn =
      toComponents K n hn ≫ componentsReflection K := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  cases b <;> simp [reflectIndex_next, next_reflectNodeIndex]

/-- Reflection respects the node leg with both original branches exchanged. -/
theorem reflection_toNodes :
    branchesReflection K ≫ toNodes K n = toNodes K n ≫ nodesReflection K := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  simp

/-- Reflecting the normalization twice restores every original component coordinate. -/
@[reassoc] theorem componentsReflection_involutive :
    componentsReflection (n := n) K ≫ componentsReflection K = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp only [componentι_reflection_assoc, componentι_reflection,
    reflectIndex_reflectIndex, Category.comp_id]
  change r ≫ (ProjectiveLine.endpointReversalOverIso K).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

/-- Reflecting the branch coproduct twice restores its original labels. -/
@[reassoc] theorem branchesReflection_involutive :
    branchesReflection (n := n) K ≫ branchesReflection K = 𝟙 _ := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  simp

/-- Reflecting the nodes twice restores every original node. -/
@[reassoc] theorem nodesReflection_involutive :
    nodesReflection (n := n) K ≫ nodesReflection K = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  change nodeι K n i ≫ _ = nodeι K n i ≫ _
  simp

end FLT.Mazur.PolygonPinching
