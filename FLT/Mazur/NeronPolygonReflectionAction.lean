/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NeronPolygonDihedralRelations
public import FLT.Mazur.ProjectiveLineReflectionAction
public import FLT.Mazur.PolygonUniversalAction

/-!
# Reflection intertwines the whole polygon action with group inversion

Both the torus parameter and cyclic component index are inverted. The
relation descends through the actual tensor pinching pushout, retaining
all original normalization components and nodes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open MonObj GrpObj
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] {n : ℕ} [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "G" => PolygonSplitGroup.model K n
local notation "T" => MultiplicativeGroupScheme.gm K
local notation "r" => polygonReflection K hn p q h
local notation "a" => PolygonUniversalAction.act K n hn p q h
open PolygonUniversalAction

/-- The original normalization input intertwines reflection and full group inversion. -/
theorem normalizationInput_reflection :
    normalizationInput K n p ≫ r =
      (PolygonSplitGroup.inversion K n ⊗ₘ componentsReflection K) ≫
        normalizationInput K n p := by
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n => T)
    (fun _ : Fin n => component K)
  intro b i
  change (PolygonSplitGroup.component K n b ⊗ₘ componentι K n i) ≫ _ =
    (PolygonSplitGroup.component K n b ⊗ₘ componentι K n i) ≫ _
  rw [component_normalizationInput_assoc, componentι_polygonReflection,
    tensorHom_comp_tensorHom_assoc, PolygonSplitGroup.component_inversion,
    componentι_reflection, ← tensorHom_comp_tensorHom_assoc,
    component_normalizationInput]
  rw [← ProjectiveLine.universalAction_endpointReversal_assoc,
    reflectIndex_rotateIndex]

/-- Reflection also intertwines the full node input, including its parameter projection. -/
theorem nodeInput_reflection :
    nodeInput K n q ≫ r =
      (PolygonSplitGroup.inversion K n ⊗ₘ nodesReflection K) ≫ nodeInput K n q := by
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n => T)
    (fun _ : Fin n => point K)
  intro b i
  change (PolygonSplitGroup.component K n b ⊗ₘ nodeι K n i) ≫ _ =
    (PolygonSplitGroup.component K n b ⊗ₘ nodeι K n i) ≫ _
  rw [component_nodeInput_assoc, nodeι_polygonReflection,
    tensorHom_comp_tensorHom_assoc, PolygonSplitGroup.component_inversion,
    nodeι_reflection, ← whiskerRight_comp_tensorHom_assoc, component_nodeInput]
  simp only [whiskerRight_snd_assoc, reflectNodeIndex_rotateIndex]

/-- On the whole realized polygon, reflection inverts the original smooth group parameter. -/
@[reassoc] theorem polygonAction_reflection :
    a ≫ r = (PolygonSplitGroup.inversion K n ⊗ₘ r) ≫ a := by
  apply (PolygonPinchingTensor.isPushout K n hn G p q h).hom_ext
  · rw [normalization_act_assoc, whiskerLeft_comp_tensorHom_assoc,
      components_polygonReflection, ← tensorHom_comp_whiskerLeft_assoc,
      normalization_act, normalizationInput_reflection]
  · rw [nodes_act_assoc, whiskerLeft_comp_tensorHom_assoc,
      nodes_polygonReflection, ← tensorHom_comp_whiskerLeft_assoc,
      nodes_act, nodeInput_reflection]

/-- Conjugation by the marked reflection is inverse-parameter action on the whole polygon. -/
theorem polygonReflection_conjugate_action :
    G ◁ r ≫ a ≫ r = PolygonSplitGroup.inversion K n ▷ C ≫ a := by
  rw [polygonAction_reflection, whiskerLeft_comp_tensorHom_assoc,
    polygonReflection_involutive, tensorHom_id]

end FLT.Mazur.PolygonPinching
