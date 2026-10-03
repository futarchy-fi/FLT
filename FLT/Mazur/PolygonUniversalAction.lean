/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicPinchingRotation
public import FLT.Mazur.PolygonPinchingTensor
public import FLT.Mazur.PolygonSplitGroup
public import FLT.Mazur.ProjectiveLineActionEndpoints

/-!
# The whole-polygon morphism of the split smooth group

On a multiplicative-group component and a normalization component, scale the
projective-line coordinate and rotate the index. Fixed endpoints make this a
pinching cocone, which descends by the tensor pushout. Action laws are separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
universe u
namespace FLT.Mazur.PolygonUniversalAction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The split smooth parameter group. -/
abbrev G := PolygonSplitGroup.model K n
/-- One multiplicative-group component. -/
abbrev gm := MultiplicativeGroupScheme.gm K
/-- Scale each normalization component and rotate its index. -/
def normalizationInput : G K n ⊗ components K n ⟶ C :=
  (PolygonSplitGroup.productCofanIsColimit (fun _ : ZMod n ↦ gm K)
    (fun _ : Fin n ↦ component K)).desc (Cofan.mk _ fun ij ↦
      ProjectiveLineUniversalAction.act K ≫ componentι K n (rotateIndex ij.1 ij.2) ≫ p)
/-- Rotate nodes, forgetting the multiplicative parameter. -/
def nodeInput : G K n ⊗ nodes K n ⟶ C :=
  (PolygonSplitGroup.productCofanIsColimit (fun _ : ZMod n ↦ gm K)
    (fun _ : Fin n ↦ point K)).desc (Cofan.mk _ fun ij ↦
      snd (gm K) (point K) ≫ nodeι K n (rotateIndex ij.1 ij.2) ≫ q)
@[reassoc] theorem component_normalizationInput (a : ZMod n) (i : Fin n) :
    (PolygonSplitGroup.component K n a ⊗ₘ componentι K n i) ≫ normalizationInput K n p =
      ProjectiveLineUniversalAction.act K ≫ componentι K n (rotateIndex a i) ≫ p :=
  (PolygonSplitGroup.productCofanIsColimit (fun _ : ZMod n ↦ gm K)
    (fun _ : Fin n ↦ component K)).fac _ ⟨a, i⟩
@[reassoc] theorem component_nodeInput (a : ZMod n) (i : Fin n) :
    (PolygonSplitGroup.component K n a ⊗ₘ nodeι K n i) ≫ nodeInput K n q =
      snd (gm K) (point K) ≫ nodeι K n (rotateIndex a i) ≫ q :=
  (PolygonSplitGroup.productCofanIsColimit (fun _ : ZMod n ↦ gm K)
    (fun _ : Fin n ↦ point K)).fac _ ⟨a, i⟩
include h in
theorem input_condition :
    G K n ◁ toComponents K n hn ≫ normalizationInput K n p =
      G K n ◁ toNodes K n ≫ nodeInput K n q := by
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n ↦ gm K)
    (fun _ : Fin n × Bool ↦ point K)
  intro a ⟨i, b⟩
  change (PolygonSplitGroup.component K n a ⊗ₘ branchι K n i b) ≫ _ =
    (PolygonSplitGroup.component K n a ⊗ₘ branchι K n i b) ≫ _
  rw [tensorHom_comp_whiskerLeft_assoc, tensorHom_comp_whiskerLeft_assoc,
    branchι_toNodes, component_nodeInput]
  cases b
  · rw [branchι_toComponents_zero, ← whiskerLeft_comp_tensorHom_assoc,
      component_normalizationInput]
    have he := ProjectiveLineActionEndpoints.section_act K false
    change gm K ◁ ProjectiveLine.zeroSection K ≫ ProjectiveLineUniversalAction.act K =
      snd (gm K) (point K) ≫ ProjectiveLine.zeroSection K at he
    rw [reassoc_of% he]
    have hw := congrArg (fun t ↦ branchι K n (rotateIndex a i) false ≫ t) h.w
    simpa only [Category.assoc, branchι_toComponents_zero_assoc, branchι_toNodes_assoc] using
      congrArg (snd (gm K) (point K) ≫ ·) hw
  · rw [branchι_toComponents_infinity, ← whiskerLeft_comp_tensorHom_assoc,
      component_normalizationInput]
    have he := ProjectiveLineActionEndpoints.section_act K true
    change gm K ◁ ProjectiveLine.infinitySection K ≫ ProjectiveLineUniversalAction.act K =
      snd (gm K) (point K) ≫ ProjectiveLine.infinitySection K at he
    rw [reassoc_of% he, rotateIndex_next]
    have hw := congrArg (fun t ↦ branchι K n (rotateIndex a i) true ≫ t) h.w
    simpa only [Category.assoc, branchι_toComponents_infinity_assoc, branchι_toNodes_assoc] using
      congrArg (snd (gm K) (point K) ≫ ·) hw

/-- The whole-polygon morphism descended from scaling and cyclic rotation. -/
def act : G K n ⊗ C ⟶ C :=
  (PolygonPinchingTensor.isPushout K n hn (G K n) p q h).desc
    (normalizationInput K n p) (nodeInput K n q) (input_condition K n hn p q h)
@[reassoc (attr := simp)] theorem normalization_act :
    G K n ◁ p ≫ act K n hn p q h = normalizationInput K n p :=
  (PolygonPinchingTensor.isPushout K n hn (G K n) p q h).inl_desc _ _ _
@[reassoc (attr := simp)] theorem nodes_act :
    G K n ◁ q ≫ act K n hn p q h = nodeInput K n q :=
  (PolygonPinchingTensor.isPushout K n hn (G K n) p q h).inr_desc _ _ _
@[reassoc] theorem component_act (a : ZMod n) (i : Fin n) :
    (PolygonSplitGroup.component K n a ⊗ₘ (componentι K n i ≫ p)) ≫ act K n hn p q h =
      ProjectiveLineUniversalAction.act K ≫ componentι K n (rotateIndex a i) ≫ p := by
  rw [← tensorHom_comp_whiskerLeft_assoc, normalization_act, component_normalizationInput]
@[reassoc] theorem node_act (a : ZMod n) (i : Fin n) :
    (PolygonSplitGroup.component K n a ⊗ₘ (nodeι K n i ≫ q)) ≫ act K n hn p q h =
      snd (gm K) (point K) ≫ nodeι K n (rotateIndex a i) ≫ q := by
  rw [← tensorHom_comp_whiskerLeft_assoc, nodes_act, component_nodeInput]
end FLT.Mazur.PolygonUniversalAction
