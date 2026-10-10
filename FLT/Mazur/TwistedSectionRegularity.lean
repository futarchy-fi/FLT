/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwistedSectionPushforward

/-!
# Regularity through tensor duality and the sheaf adjunction

A twisted section is regular exactly when the total-space adjoint of its
direct-image morphism is monic. This is a total-space statement; local
splitting of the morphism on the base is a separate fiberwise criterion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
variable {X S : Scheme.{u}}

/-- Tensor duality preserves and reflects regularity of a section. -/
theorem lineHomSectionEquiv_mono_iff (L : X.Modules) {B : X.Modules}
    (hB : LocallyFreeRankOne B) (a : moduleSheafDual B ⟶ L) :
    Mono (globalSectionHom (tensor L B) (lineHomSectionEquiv L hB a)) ↔ Mono a := by
  rw [lineHomSectionEquiv_hom, mono_comp_iff_of_isIso]
  exact (lineTensorEquivalence hB).functor.mono_map_iff_mono a

/-- A given tensor section is regular exactly when its dual-line morphism is monic. -/
theorem lineHomSectionEquiv_symm_mono_iff (L : X.Modules) {B : X.Modules}
    (hB : LocallyFreeRankOne B) (s : Γ(tensor L B, ⊤)) :
    Mono ((lineHomSectionEquiv L hB).symm s) ↔
      Mono (globalSectionHom (tensor L B) s) := by
  simpa only [Equiv.apply_symm_apply] using
    (lineHomSectionEquiv_mono_iff L hB ((lineHomSectionEquiv L hB).symm s)).symm

/-- The actual adjoint detects regularity, with no flatness hypothesis on the base map. -/
theorem twistedSectionPushforwardEquiv_regular_iff (f : X ⟶ S) (L : X.Modules)
    {B : S.Modules} (hB : LocallyFreeRankOne B)
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    Mono (((pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (twistedSectionPushforwardEquiv f L hB s)) ↔
        Mono (globalSectionHom (tensor L ((pullback f).obj B)) s) := by
  rw [twistedSectionPushforwardEquiv_adjoint, mono_comp_iff_of_isIso]
  exact lineHomSectionEquiv_symm_mono_iff L (hB.pullback f) s

/-- Regularity of the recovered section can be checked directly on the counit composite. -/
theorem twistedSectionPushforwardEquiv_symm_regular_iff (f : X ⟶ S) (L : X.Modules)
    {B : S.Modules} (hB : LocallyFreeRankOne B)
    (a : moduleSheafDual B ⟶ (pushforward f).obj L) :
    Mono (globalSectionHom (tensor L ((pullback f).obj B))
      ((twistedSectionPushforwardEquiv f L hB).symm a)) ↔
        Mono ((pullback f).map a ≫ (pullbackPushforwardAdjunction f).counit.app L) := by
  simpa only [Equiv.apply_symm_apply, Adjunction.homEquiv_symm_apply] using
    (twistedSectionPushforwardEquiv_regular_iff f L hB
      ((twistedSectionPushforwardEquiv f L hB).symm a)).symm

end FLT.Mazur.FCurve
