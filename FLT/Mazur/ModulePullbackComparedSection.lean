/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Sections of an isomorphism with a prescribed pullback comparison

The equality of the actual pullback isomorphisms gives the corresponding
section identity without expanding geometric line constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A prescribed pullback comparison transports original global sections. -/
theorem pullbackComparedSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L M : Y.Modules} {N : X.Modules} (e : L ≅ M)
    (a : (pullback f).obj L ≅ N) (b : (pullback f).obj M ≅ N)
    (he : (pullback f).mapIso e = a ≪≫ b.symm) (s : Γ(L, ⊤)) :
    b.hom.app ⊤ (pullGlobal f M (e.hom.app ⊤ s)) =
      a.hom.app ⊤ (pullGlobal f L s) := by
  rw [← pullGlobal_naturality]
  have hh : (pullback f).map e.hom ≫ b.hom = a.hom := by
    rw [← Functor.mapIso_hom, he]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g ↦ g.app ⊤ (pullGlobal f L s)) hh

end FLT.Mazur.FCurve
