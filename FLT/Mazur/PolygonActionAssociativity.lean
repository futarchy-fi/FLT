/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionUnit
public import FLT.Mazur.ProjectiveLineActionAssociativity

/-!
# Associativity of the whole-polygon action

Flat tensoring preserves the epic normalization. On each triple of components,
the action law is projective-line associativity and addition of rotation indices.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonActionAssociativity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonUniversalAction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
theorem tensor_normalization_epi (X : Over (Spec (.of K))) [Flat X.hom] : Epi (X ◁ p) := by
  have : Epi (X ◁ toNodes K n) := by
    apply epi_of_epi_fac (f := X ◁ PinchingPullbackTransport.nodeRetraction K n) (h := 𝟙 _)
    rw [← whiskerLeft_comp, PinchingPullbackTransport.nodeRetraction_toNodes, whiskerLeft_id]
  exact (PolygonPinchingTensor.isPushout K n hn X p q h).epi_inl_of_epi

theorem assoc_act : μ[G K n] ▷ C ≫ act K n hn p q h =
    (α_ (G K n) (G K n) C).hom ≫ G K n ◁ act K n hn p q h ≫ act K n hn p q h := by
  let : Flat (G K n ⊗ G K n).hom := by
    change Flat (pullback.fst _ _ ≫ _)
    infer_instance
  let : Epi ((G K n ⊗ G K n) ◁ p) := tensor_normalization_epi K n hn p q h _
  apply (cancel_epi ((G K n ⊗ G K n) ◁ p)).mp
  apply PolygonSplitGroup.triple_hom_ext (fun _ : ZMod n ↦ gm K)
    (fun _ : ZMod n ↦ gm K) (fun _ : Fin n ↦ component K)
  intro a b i
  change ((PolygonSplitGroup.component K n a ⊗ₘ PolygonSplitGroup.component K n b) ⊗ₘ
    componentι K n i) ≫ _ = _
  rw [tensorHom_comp_whiskerLeft_assoc, tensorHom_comp_whiskerLeft_assoc,
    tensorHom_comp_whiskerRight_assoc, PolygonSplitGroup.component_mul,
    ← whiskerRight_comp_tensorHom_assoc, component_act]
  rw [associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc]
  erw [component_act K n hn p q h b i]
  rw [← whiskerLeft_comp_tensorHom_assoc]
  erw [component_act K n hn p q h a (rotateIndex b i)]
  simp only [← Category.assoc, ProjectiveLineActionAssociativity.assoc_act,
    ← rotateIndex_add, add_comm]
end FLT.Mazur.PolygonActionAssociativity
