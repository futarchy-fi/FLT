/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePushforwardSectionTransition
public import FLT.Mazur.SchemeModulePullbackUnitSections
public import FLT.Mazur.ModulePullbackStageIso

/-!
# Coherence of actual pushed-forward transitions

The adjunction transition respects comparison squares and sends the original
restriction unit to the unit of the composite stage map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p)

/-- A commuting pullback square gives the actual commuting direct-image square. -/
theorem pushforwardSectionTransition_square {M M' : Y.Modules} {N N' : X.Modules}
    (b : M ⟶ M') (a : N ⟶ N') (c : (pullback r).obj M' ⟶ N')
    (d : (pullback r).obj M ⟶ N) (hs : (pullback r).map b ≫ c = d ≫ a) :
    (pushforward q).map b ≫ pushforwardSectionTransition p q r h c =
      pushforwardSectionTransition p q r h d ≫ (pushforward p).map a := by
  subst p
  unfold pushforwardSectionTransition moduleSectionTransport
  ext U s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app, eqToHom_refl,
    op_id]
  erw [N'.presheaf.map_id, N.presheaf.map_id]
  have hn := congrArg (fun k ↦ k.app (q ⁻¹ᵁ U) s)
    ((pullbackPushforwardAdjunction r).unit.naturality b)
  have hh := congrArg (fun k ↦ k.app (r ⁻¹ᵁ (q ⁻¹ᵁ U))
    (((pullbackPushforwardAdjunction r).unit.app M).app (q ⁻¹ᵁ U) s)) hs
  change c.app _ (((pullbackPushforwardAdjunction r).unit.app M').app _ (b.app _ s)) = _
  change ((pullbackPushforwardAdjunction r).unit.app M').app _ (b.app _ s) =
    ((pullback r).map b).app _
      (((pullbackPushforwardAdjunction r).unit.app M).app _ s) at hn
  rw [hn]
  exact hh

/-- The transition of actual restrictions carries the original unit to the next unit. -/
theorem unit_pushforwardSectionTransition (L : S.Modules) :
    (pullbackPushforwardAdjunction q).unit.app L ≫
      pushforwardSectionTransition p q r h
        (pullbackStageIso p q r h L).hom =
      (pullbackPushforwardAdjunction p).unit.app L := by
  rw [pullbackStageIso_hom]
  subst p
  unfold pushforwardSectionTransition moduleSectionTransport
  ext U s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app, eqToHom_refl,
    op_id]
  erw [((pullback (r ≫ q)).obj L).presheaf.map_id]
  exact SchemeModulePullbackUnitSections.comp_unit r q L U s

end FLT.Mazur.FCurve
