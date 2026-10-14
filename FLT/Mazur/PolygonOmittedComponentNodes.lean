/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContraction
public import FLT.Mazur.CyclicOmittedEdgeConstancy

/-!
# Constant omitted components identify all original node morphisms

The original pinching equations and constancy on omitted complete components
force all nodes to have one image. In particular the retained component's
zero and infinity have the same image, giving the one-gon descent relation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOmittedComponentNodes
open PolygonPinching PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C Y : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (f : C ⟶ Y)

include h in
omit [NeZero n] in
/-- The original zero endpoint gives the original node value. -/
@[reassoc] theorem zero_component (j : Fin n) :
    ProjectiveLine.zeroSection K ≫ componentι K n j ≫ p ≫ f = nodeι K n j ≫ q ≫ f := by
  have H := congrArg (fun g ↦ branchι K n j false ≫ g ≫ f) h.w
  simpa only [branchι_toComponents_zero_assoc, branchι_toNodes_assoc, Category.assoc] using H

include h in
omit [NeZero n] in
/-- The original infinity endpoint gives the preceding node value. -/
@[reassoc] theorem infinity_component (j : Fin n) :
    ProjectiveLine.infinitySection K ≫ componentι K n (next hn j) ≫ p ≫ f =
      nodeι K n j ≫ q ≫ f := by
  have H := congrArg (fun g ↦ branchι K n j true ≫ g ≫ f) h.w
  simpa only [branchι_toComponents_infinity_assoc, branchι_toNodes_assoc,
    Category.assoc] using H

variable (i : Fin n)
  (hc : ∀ j, j ≠ i → componentι K n j ≫ p ≫ f =
    componentToPoint K ≫ ProjectiveLine.zeroSection K ≫ componentι K n j ≫ p ≫ f)

include h hc

/-- All original node morphisms agree when every other complete component is constant. -/
theorem node_eq (j : Fin n) : nodeι K n j ≫ q ≫ f = nodeι K n i ≫ q ≫ f := by
  apply eq_of_omitted_edge hn (fun j ↦ nodeι K n j ≫ q ≫ f) i _ j
  intro k hk
  rw [← infinity_component K n hn p q h f k]
  rw [hc (next hn k) hk, infinity_componentToPoint_assoc]
  exact (zero_component K n hn p q h f (next hn k)).symm

/-- The retained complete component's endpoints satisfy the one-gon pinching relation. -/
theorem retained_endpoints :
    ProjectiveLine.zeroSection K ≫ componentι K n i ≫ p ≫ f =
      ProjectiveLine.infinitySection K ≫ componentι K n i ≫ p ≫ f := by
  have hi : next hn (i - 1) = i := by rw [next_eq_add_one, sub_add_cancel]
  have H := infinity_component K n hn p q h f (i - 1)
  rw [hi, node_eq K n hn p q h f i hc] at H
  exact (zero_component K n hn p q h f i).trans H.symm

/-- Each omitted component is the constant map at the common original node value. -/
theorem omitted_eq_node {j : Fin n} (hj : j ≠ i) :
    componentι K n j ≫ p ≫ f = componentToPoint K ≫ nodeι K n i ≫ q ≫ f := by
  rw [hc j hj, zero_component K n hn p q h f j, node_eq K n hn p q h f i hc]

end FLT.Mazur.PolygonOmittedComponentNodes
