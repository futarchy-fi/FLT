/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackSectionCoherence
public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Pulled-back trivializations on actual sections

The local trivialization transports an adjunction-unit section to the
pullback of its original chart coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModulePullbackSectionCoherence

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)

/-- The pulled-back local basis evaluates actual chart sections by scalar pullback. -/
theorem modulePullbackTrivialization_chartSection
    (e : M.restrict U.ι ≅ structureModule U.toScheme) (s : Γ(M, U)) :
    (modulePullbackTrivialization f e).hom.app ⊤
        (chartSection ((pullback f).obj M) (f ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction f).unit.app M).app U s)) =
      (f ∣_ U).appTop (e.hom.app ⊤ (chartSection M U s)) := by
  simp only [modulePullbackTrivialization, Iso.trans_hom, Functor.mapIso_hom,
    Hom.comp_app, ConcreteCategory.comp_apply]
  rw [open_unit_top]
  have hn := congrArg (fun a ↦ a.app ⊤ (chartSection M U s))
    ((pullbackPushforwardAdjunction (f ∣_ U)).unit.naturality e.hom).symm
  change ((pullback (f ∣_ U)).map e.hom).app ⊤
    (((pullbackPushforwardAdjunction (f ∣_ U)).unit.app _).app ⊤ _) =
    (((pullbackPushforwardAdjunction (f ∣_ U)).unit.app _).app ⊤
      (e.hom.app ⊤ (chartSection M U s))) at hn
  rw [hn]
  exact modulePullbackUnitIso_unit (f ∣_ U) ⊤ _

/-- Evaluation of a pulled global section is pullback of its original local coefficient. -/
theorem modulePullbackTrivialization_pullGlobal
    (e : M.restrict U.ι ≅ structureModule U.toScheme) (s : Γ(M, ⊤)) :
    (modulePullbackTrivialization f e).hom.app ⊤
        (((pullback f).obj M).presheaf.map (homOfLE le_top).op (pullGlobal f M s)) =
      (f ∣_ U).appTop (e.hom.app ⊤ (M.presheaf.map (homOfLE le_top).op s)) := by
  have hn := ConcreteCategory.congr_hom
    (((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op) s
  change (((pullbackPushforwardAdjunction f).unit.app M).app U
    (M.presheaf.map (homOfLE le_top).op s)) =
    ((pullback f).obj M).presheaf.map (homOfLE le_top).op (pullGlobal f M s) at hn
  have he := modulePullbackTrivialization_chartSection f M U e
    (M.presheaf.map (homOfLE le_top).op s)
  rw [hn] at he
  simp only [chartSection, ← Functor.map_comp_apply] at he
  convert he using 1 <;> congr 3

end FLT.Mazur.FCurve
