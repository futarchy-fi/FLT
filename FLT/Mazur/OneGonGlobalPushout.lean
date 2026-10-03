/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAffineNormalization
public import FLT.Mazur.PolygonCyclicPushout

/-!
# The specified one-gon pinching pushout

Affine pinching descent and the full Laurent chart give descent to arbitrary
schemes, and then the exact pinching pushout over the coefficient field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.OneGonGlobalPushout
open OneGonTransition OneGonAffineCover OneGonAffineNormalization
open OneGonNormalization PinchingAffineDescent PolygonNodePresentation
variable (K : Type u) [Field K]
variable {Y : Scheme.{u}} (f : ProjectiveLine.scheme K ⟶ Y)
  (w : ProjectiveLine.zero K ≫ f = ProjectiveLine.infinity K ≫ f)

/-- Descent on the pinched affine chart. -/
def nodeDesc : OneGonGluing.nodeChart K ⟶ Y :=
  (OneGonPinchingDescent.oneGon_desc K (alpha K ≫ f) (by simp [w])).choose

@[reassoc (attr := simp)]
theorem oneBranch_nodeDesc : oneBranch K ≫ nodeDesc K f w = alpha K ≫ f :=
  (OneGonPinchingDescent.oneGon_desc K (alpha K ≫ f) (by simp [w])).choose_spec.1

/-- Agreement on the actual puncture of the equalizer chart. -/
theorem desc_condition : bPuncture K ≫ nodeDesc K f w =
    toTorus K ≫ (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ f := by
  rw [← OneGonPinchingDescent.puncture_oneBranch, Category.assoc,
    oneBranch_nodeDesc, ← Category.assoc, puncture_alpha]
  simp only [Category.assoc]

/-- Arbitrary-target descent on the whole glued one-gon. -/
def schemeDesc : OneGonGluing.scheme K ⟶ Y :=
  pushout.desc (nodeDesc K f w)
    ((ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ f) (desc_condition K f w)

@[reassoc (attr := simp)]
theorem node_schemeDesc : OneGonGluing.node K ≫ schemeDesc K f w = nodeDesc K f w :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem torus_schemeDesc : OneGonGluing.torus K ≫ schemeDesc K f w =
    (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ f := pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem normalization_schemeDesc : normalization K ≫ schemeDesc K f w = f := by
  apply BinaryOpenDescent.hom_ext (alpha K)
    (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) (covers K)
  · rw [alpha_normalization_assoc, node_schemeDesc, oneBranch_nodeDesc]
  · rw [← Category.assoc, torus_normalization, torus_schemeDesc]

/-- Normalization detects equality even for nonseparated targets. -/
theorem scheme_hom_ext (d e : OneGonGluing.scheme K ⟶ Y)
    (h : normalization K ≫ d = normalization K ≫ e) : d = e := by
  apply pushout.hom_ext
  · change OneGonGluing.node K ≫ d = OneGonGluing.node K ≫ e
    apply OneGonPinchingDescent.hom_ext K
    rw [← Category.assoc, ← Category.assoc, ← alpha_normalization,
      Category.assoc, Category.assoc, h]
  · change OneGonGluing.torus K ≫ d = OneGonGluing.torus K ≫ e
    rw [← torus_normalization]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ t) h

variable (hn : 0 < 1) {C : Over (Spec (.of K))}
  (p : PolygonPinching.components K 1 ⟶ C) (q : PolygonPinching.nodes K 1 ⟶ C)
  (hpq : PolygonPinching.toComponents K 1 hn ≫ p = PolygonPinching.toNodes K 1 ≫ q)

/-- The unique component of a compatible input cocone. -/
def input : ProjectiveLine.scheme K ⟶ C.left :=
  PolygonCyclicPushout.inputComponent K 1 p 0

include hpq in
/-- The input cocone identifies precisely zero and infinity. -/
theorem input_condition : ProjectiveLine.zero K ≫ input K p =
    ProjectiveLine.infinity K ≫ input K p := by
  have h := PolygonCyclicPushout.input_condition K 1 hn p q hpq 0
  simpa only [input, show finRotate 1 0 = 0 from Subsingleton.elim _ _] using h

/-- Descent of the input cocone in schemes over K. -/
def desc : polygon K ⟶ C :=
  Over.homMk (schemeDesc K (input K p) (input_condition K hn p q hpq)) (by
    change schemeDesc K _ _ ≫ C.hom = OneGonGluing.toBase K
    apply scheme_hom_ext K
    rw [normalization_schemeDesc_assoc, normalization_toBase]
    exact (PolygonPinching.componentι K 1 0 ≫ p).w)

@[reassoc (attr := simp)]
theorem normalization_desc : normalizationOver K ≫ desc K hn p q hpq = p := by
  apply Sigma.hom_ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change PolygonPinching.componentι K 1 0 ≫ normalizationOver K ≫ _ = _
  rw [componentι_normalizationOver_assoc]
  apply Over.OverMorphism.ext
  exact normalization_schemeDesc K _ _

@[reassoc (attr := simp)]
theorem nodes_desc : nodes K ≫ desc K hn p q hpq = q := by
  apply Sigma.hom_ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change PolygonPinching.nodeι K 1 0 ≫ nodes K ≫ _ = _
  apply Over.OverMorphism.ext
  change (PolygonPinching.nodeι K 1 0 ≫ nodes K).left ≫ _ = _
  rw [nodeι_nodes, ← zero_normalization, Category.assoc]
  change ProjectiveLine.zero K ≫ normalization K ≫ schemeDesc K _ _ = _
  rw [normalization_schemeDesc]
  exact PolygonCyclicPushout.zero_input K 1 hn p q hpq 0

/-- Equality in Over is detected by the specified normalization. -/
theorem hom_ext (d e : polygon K ⟶ C)
    (h : normalizationOver K ≫ d = normalizationOver K ≫ e) : d = e := by
  apply Over.OverMorphism.ext
  apply scheme_hom_ext K
  have hh := congrArg (fun t ↦ PolygonPinching.componentι K 1 0 ≫ t) h
  rw [← Category.assoc, ← Category.assoc, componentι_normalizationOver] at hh
  exact congrArg (fun t ↦ t.left) hh

/-- The exact one-component pinching cocone is a pushout over K. -/
theorem isPushout : IsPushout (PolygonPinching.toComponents K 1 hn)
    (PolygonPinching.toNodes K 1) (normalizationOver K) (nodes K) := by
  refine ⟨⟨cocone K hn⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ desc K hn s.inl s.inr s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    exact normalization_desc K hn s.inl s.inr s.condition
  · intro s
    exact nodes_desc K hn s.inl s.inr s.condition
  · intro s m hm _
    exact hom_ext K m _ (hm.trans (normalization_desc ..).symm)

end FLT.Mazur.OneGonGlobalPushout
