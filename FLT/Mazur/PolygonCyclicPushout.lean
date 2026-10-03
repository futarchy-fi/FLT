/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicDescent

/-!
# The specified cyclic pinching pushout for at least two components

Arbitrary-target descent on the cyclic atlas gives the pushout in schemes
over K, for the exact normalization and node maps of the pinching diagram.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonCyclicPushout

open PolygonCyclicAtlas

variable (K : Type u) [Field K] (n : ℕ) (h : 2 ≤ n) (hn : 0 < n)
  {C : Over (Spec (.of K))} (f : PolygonPinching.components K n ⟶ C)
  (q : PolygonPinching.nodes K n ⟶ C)
  (w : PolygonPinching.toComponents K n hn ≫ f = PolygonPinching.toNodes K n ≫ q)

/-- The specified component maps of an input cocone. -/
def inputComponent (i : Fin n) : ProjectiveLine.scheme K ⟶ C.left :=
  (PolygonPinching.componentι K n i ≫ f).left

include w in
/-- The zero endpoint of each input component is the specified node map. -/
theorem zero_input (i : Fin n) : ProjectiveLine.zero K ≫ inputComponent K n f i =
    (PolygonPinching.nodeι K n i ≫ q).left := by
  have hw := congrArg (fun t ↦ PolygonPinching.branchι K n i false ≫ t) w
  rw [← Category.assoc, ← Category.assoc, PolygonPinching.branchι_toComponents_zero,
    PolygonPinching.branchι_toNodes, Category.assoc] at hw
  exact congrArg (fun t ↦ t.left) hw

include w in
/-- Infinity on the successor component is the same specified node map. -/
theorem infinity_input (i : Fin n) :
    ProjectiveLine.infinity K ≫ inputComponent K n f (finRotate n i) =
      (PolygonPinching.nodeι K n i ≫ q).left := by
  have hw := congrArg (fun t ↦ PolygonPinching.branchι K n i true ≫ t) w
  rw [← Category.assoc, ← Category.assoc, PolygonPinching.branchι_toComponents_infinity,
    PolygonPinching.branchι_toNodes, next_eq_rotate, Category.assoc] at hw
  exact congrArg (fun t ↦ t.left) hw

include w in
/-- The input components satisfy exactly the cyclic endpoint relation. -/
theorem input_condition (i : Fin n) : ProjectiveLine.zero K ≫ inputComponent K n f i =
    ProjectiveLine.infinity K ≫ inputComponent K n f (finRotate n i) :=
  (zero_input K n hn f q w i).trans (infinity_input K n hn f q w i).symm

/-- The descended morphism of the input cocone, over the coefficient field. -/
def desc : polygon K n h ⟶ C :=
  Over.homMk (PolygonCyclicDescent.desc K n h (inputComponent K n f)
    (input_condition K n hn f q w)) (by
      change PolygonCyclicDescent.desc K n h _ _ ≫ C.hom = toBase K n h
      apply PolygonCyclicDescent.hom_ext K n h
      intro i
      rw [PolygonCyclicDescent.componentMap_desc_assoc, componentMap_toBase]
      exact (PolygonPinching.componentι K n i ≫ f).w)

@[reassoc (attr := simp)]
theorem normalization_desc : normalization K n h ≫ desc K n h hn f q w = f := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K n i ≫ normalization K n h ≫ _ = _
  rw [componentι_normalization_assoc]
  apply Over.OverMorphism.ext
  exact PolygonCyclicDescent.componentMap_desc K n h _ _ i

@[reassoc (attr := simp)]
theorem nodes_desc : nodes K n h ≫ desc K n h hn f q w = q := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.nodeι K n i ≫ nodes K n h ≫ _ = _
  apply Over.OverMorphism.ext
  change (PolygonPinching.nodeι K n i ≫ nodes K n h).left ≫ _ = _
  rw [nodeι_nodes, ← zero_componentMap, Category.assoc]
  change ProjectiveLine.zero K ≫ componentMap K n h i ≫
    PolygonCyclicDescent.desc K n h _ _ = _
  rw [PolygonCyclicDescent.componentMap_desc]
  exact zero_input K n hn f q w i

/-- Equality of over-morphisms is detected on the normalization. -/
theorem hom_ext (d e : polygon K n h ⟶ C)
    (he : normalization K n h ≫ d = normalization K n h ≫ e) : d = e := by
  apply Over.OverMorphism.ext
  apply PolygonCyclicDescent.hom_ext K n h
  intro i
  have hh := congrArg (fun t ↦ PolygonPinching.componentι K n i ≫ t) he
  rw [← Category.assoc, ← Category.assoc, componentι_normalization] at hh
  exact congrArg (fun t ↦ t.left) hh

/-- The exact specified cyclic pinching cocone is a pushout for n ≥ 2. -/
theorem isPushout : IsPushout (PolygonPinching.toComponents K n hn)
    (PolygonPinching.toNodes K n) (normalization K n h) (nodes K n h) := by
  refine ⟨⟨cocone K n h hn⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ desc K n h hn s.inl s.inr s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    exact normalization_desc K n h hn s.inl s.inr s.condition
  · intro s
    exact nodes_desc K n h hn s.inl s.inr s.condition
  · intro s m hm _
    exact hom_ext K n h m _ (hm.trans (normalization_desc ..).symm)

end FLT.Mazur.PolygonCyclicPushout
