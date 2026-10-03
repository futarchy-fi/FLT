/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonUniversalAction
public import FLT.Mazur.ProjectiveLineActionSpecialization

/-!
# The identity acts trivially on the whole polygon

The normalization is epic because the node leg of the pinching span splits.
Its component formulas reduce the unit law to projective-line scaling at one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
universe u
namespace FLT.Mazur.PolygonActionUnit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonUniversalAction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
omit [NeZero n] in
theorem normalization_epi : Epi p := by
  have : Epi (toNodes K n) := epi_of_epi_fac (PinchingPullbackTransport.nodeRetraction_toNodes K n)
  exact h.epi_inl_of_epi

theorem unit_act : η[G K n] ▷ C ≫ act K n hn p q h = (λ_ C).hom := by
  let : Epi p := normalization_epi K n hn p q h
  apply (cancel_epi (λ_ C).inv).mp
  rw [Iso.inv_hom_id]
  apply (cancel_epi p).mp
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ p ≫ (λ_ C).inv ≫ _ = componentι K n i ≫ p ≫ 𝟙 C
  rw [← Category.assoc (componentι K n i) p,
    leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc]
  change (λ_ (component K)).inv ≫
    ((PolygonSplitGroup.identity K n) ⊗ₘ (componentι K n i ≫ p)) ≫ _ = _
  rw [PolygonSplitGroup.identity, ← whiskerRight_comp_tensorHom_assoc, component_act]
  rw [← Category.assoc (η[gm K] ▷ component K),
    ProjectiveLineActionSpecialization.unit_act]
  simp
end FLT.Mazur.PolygonActionUnit
