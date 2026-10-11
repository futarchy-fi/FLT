/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Transporting actual pullback sections through line isomorphisms

Changing both line objects by specified isomorphisms transports the image of
a section under the original pullback comparison, including its original value.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Transport of the original pullback comparison carries the transported original section. -/
theorem pullbackSection_transport_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L L' : Y.Modules} {M M' : X.Modules} (l : L' ≅ L) (m : M' ≅ M)
    (e : (pullback f).obj L ≅ M) (s : Γ(L, ⊤)) :
    ((pullback f).mapIso l ≪≫ e ≪≫ m.symm).hom.app ⊤
        (pullGlobal f L' (l.inv.app ⊤ s)) =
      m.inv.app ⊤ (e.hom.app ⊤ (pullGlobal f L s)) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Hom.comp_app,
    ConcreteCategory.comp_apply, pullGlobal_naturality]
  have hs : l.hom.app ⊤ (l.inv.app ⊤ s) = s :=
    congrArg (fun k ↦ k.app ⊤ s) l.inv_hom_id
  rw [hs]

end FLT.Mazur.FCurve
