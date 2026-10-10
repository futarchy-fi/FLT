/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackSectionTransport

/-!
# Original section transition maps after pushforward

A module map over a stage morphism induces the actual transition between
the two pushed-forward modules. Its global sections use the original pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p) {M : Y.Modules} {N : X.Modules} (a : (pullback r).obj M ⟶ N)

/-- Push the original adjunction section transition to the common base scheme. -/
@[irreducible] def pushforwardSectionTransition :
    (pushforward q).obj M ⟶ (pushforward p).obj N :=
  (pushforward q).map (moduleSectionTransport r a) ≫
    (pushforwardComp r q).hom.app N ≫ (pushforwardCongr h).hom.app N

/-- The actual pushforward transition retains the original global pullback section. -/
theorem pushforwardSectionTransition_top (s : Γ(M, ⊤)) :
    (pushforwardSectionTransition p q r h a).app ⊤ s = a.app ⊤ (pullGlobal r M s) := by
  subst p
  unfold pushforwardSectionTransition
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app, eqToHom_refl,
    op_id]
  change N.presheaf.map (𝟙 (Opposite.op ⊤)) ((moduleSectionTransport r a).app ⊤ s) = _
  rw [N.presheaf.map_id]
  exact moduleSectionTransport_top r a s

end FLT.Mazur.FCurve
