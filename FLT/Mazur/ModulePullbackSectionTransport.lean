/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# A pullback morphism as a semilinear section transport

The adjunction turns a map out of a pulled-back module into transport of
sections. Preservation of a section morphism implies preservation of its
actual global value, without unfolding the pullback implementation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
variable (a : (pullback f).obj M ⟶ N)

/-- Semilinear transport associated to the actual pullback map. -/
@[irreducible] def moduleSectionTransport : M ⟶ (pushforward f).obj N :=
  (pullbackPushforwardAdjunction f).unit.app M ≫ (pushforward f).map a

/-- Global transport is the original adjunction-unit section followed by the given map. -/
theorem moduleSectionTransport_top (s : Γ(M, ⊤)) :
    (moduleSectionTransport f a).app ⊤ s = a.app ⊤ (pullGlobal f M s) := by
  unfold moduleSectionTransport
  rfl

/-- Equality of actual section morphisms transports their global values at one. -/
theorem moduleSectionTransport_section (c : structureModule Y ⟶ M)
    (d : structureModule X ⟶ N)
    (h : (pullback f).map c ≫ a = (modulePullbackUnitIso f).hom ≫ d) :
    (moduleSectionTransport f a).app ⊤ (c.app ⊤ (1 : Γ(Y, ⊤))) =
      d.app ⊤ (1 : Γ(X, ⊤)) := by
  rw [moduleSectionTransport_top, pullGlobal_hom]
  have hh := congrArg (fun k ↦ k.app ⊤
    ((modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)))) h
  have hi := congrArg (fun k ↦ k.app ⊤ (1 : Γ(X, ⊤))) (modulePullbackUnitIso f).inv_hom_id
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
    ConcreteCategory.id_apply] at hh hi
  rw [hi] at hh
  exact hh

end FLT.Mazur.FCurve
