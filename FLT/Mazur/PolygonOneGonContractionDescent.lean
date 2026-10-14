/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOmittedComponentNodes
public import FLT.Mazur.PolygonActionUnit

/-!
# Descending an actual polygon map through its one-gon contraction

A map constant on all omitted complete components descends through the explicit
one-gon contraction. The construction uses the retained normalization map and
the common original node value in the original one-gon pinching pushout.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContractionDescent
open PolygonPinching PolygonOneGonContraction PolygonOmittedComponentNodes
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C Y : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (f : C ⟶ Y) (i : Fin n)
  (hc : ∀ j, j ≠ i → componentι K n j ≫ p ≫ f =
    componentToPoint K ≫ ProjectiveLine.zeroSection K ≫ componentι K n j ≫ p ≫ f)

/-- The retained map on the single original target normalization component. -/
def normalization : components K 1 ⟶ Y := Sigma.desc fun _ ↦ componentι K n i ≫ p ≫ f

/-- The common original node map on the single target node. -/
def node : nodes K 1 ⟶ Y := Sigma.desc fun _ ↦ nodeι K n i ≫ q ≫ f

include h hc in
/-- The retained component and node maps satisfy the actual one-gon pinching equation. -/
theorem cocone : toComponents K 1 (by decide) ≫ normalization K n p f i =
    toNodes K 1 ≫ node K n q f i := by
  apply Sigma.hom_ext
  rintro ⟨j, b⟩
  change branchι K 1 j b ≫ _ = branchι K 1 j b ≫ _
  cases b
  · simp only [branchι_toComponents_zero_assoc, branchι_toNodes_assoc]
    simp only [normalization, node, componentι, nodeι, Sigma.ι_comp_desc]
    exact zero_component K n hn p q h f i
  · simp only [branchι_toComponents_infinity_assoc, branchι_toNodes_assoc]
    simp only [normalization, node, componentι, nodeι, Sigma.ι_comp_desc]
    exact (retained_endpoints K n hn p q h f i hc).symm.trans
      (zero_component K n hn p q h f i)

/-- The actual map out of the original contracted one-gon. -/
def desc : PolygonAtlas.polygon K 1 ⟶ Y :=
  (PolygonAtlas.isPushout K 1 (by decide)).desc
    (normalization K n p f i) (node K n q f i) (cocone K n hn p q h f i hc)

/-- The descent retains the full selected normalization component. -/
@[reassoc] theorem retained_desc :
    retainedComponent K ≫ desc K n hn p q h f i hc = componentι K n i ≫ p ≫ f := by
  simp [retainedComponent, desc, normalization, componentι]

/-- The descent retains the common original node morphism. -/
@[reassoc] theorem node_desc :
    targetNode K ≫ desc K n hn p q h f i hc = nodeι K n i ≫ q ≫ f := by
  simp [targetNode, desc, node, nodeι]

/-- The original map factors through the actual contraction on the entire source polygon. -/
@[reassoc] theorem contraction_desc :
    contraction K n hn p q h i ≫ desc K n hn p q h f i hc = f := by
  apply h.hom_ext
  · apply Sigma.hom_ext
    intro j
    change componentι K n j ≫ p ≫ _ = componentι K n j ≫ p ≫ f
    by_cases hj : j = i
    · subst j
      rw [retained_contraction_assoc, retained_desc]
    · rw [omitted_contraction_assoc K n hn p q h i hj, node_desc]
      exact (omitted_eq_node K n hn p q h f i hc hj).symm
  · apply Sigma.hom_ext
    intro j
    change nodeι K n j ≫ q ≫ _ = nodeι K n j ≫ q ≫ f
    rw [node_contraction_assoc, node_desc]
    exact (node_eq K n hn p q h f i hc j).symm

omit [NeZero n] in
/-- The actual contraction is epic: its retained component covers the target normalization. -/
theorem contraction_epi : Epi (contraction K n hn p q h i) := by
  constructor
  intro Z a b hab
  let _ := PolygonActionUnit.normalization_epi K 1 (by decide)
    (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
    (PolygonAtlas.isPushout K 1 (by decide))
  apply (cancel_epi (PolygonAtlas.normalization K 1)).mp
  apply Sigma.hom_ext
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  change retainedComponent K ≫ a = retainedComponent K ≫ b
  have H := congrArg (fun g ↦ componentι K n i ≫ p ≫ g) hab
  simpa only [retained_contraction_assoc] using H

/-- The descended map is the unique global factorization through the original contraction. -/
theorem desc_unique (a : PolygonAtlas.polygon K 1 ⟶ Y)
    (ha : contraction K n hn p q h i ≫ a = f) : a = desc K n hn p q h f i hc := by
  let _ := contraction_epi K n hn p q h i
  apply (cancel_epi (contraction K n hn p q h i)).mp
  rw [ha, contraction_desc]

end FLT.Mazur.PolygonOneGonContractionDescent
