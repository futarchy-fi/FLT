/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# Pullback unit composition on arbitrary opens

The geometric composition comparison preserves unit sections over every
open, so chart naturality can be checked without extending a section globally.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace FLT.Mazur.SchemeModulePullbackUnitSections

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Composition preserves iterated pullback units on every original open. -/
lemma comp_unit (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U m)) =
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun k ↦ k.app U m) h
  change (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U m)) =
    ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m) at h'
  rw [h']
  exact congrArg (fun k : (pullback (f ≫ g)).obj M ⟶ (pullback (f ≫ g)).obj M ↦
    k.app ((f ≫ g) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m))
        ((pullbackComp f g).app M).inv_hom_id

end FLT.Mazur.SchemeModulePullbackUnitSections
