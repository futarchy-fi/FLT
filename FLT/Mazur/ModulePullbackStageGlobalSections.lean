/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModulePullbackStageIso
public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# Global coordinates under the sealed stage comparison

The existing stage comparison carries iterated pullback sections to the
original direct pullback, without unfolding concrete resolved scheme models.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p) (L : S.Modules)

/-- The actual stage comparison retains the value of each pulled-back global section. -/
theorem pullbackStageIso_globalSection (s : Γ(L, ⊤)) :
    (pullbackStageIso p q r h L).hom.app ⊤
      (pullGlobal r ((pullback q).obj L) (pullGlobal q L s)) = pullGlobal p L s := by
  have hc := congrArg (fun z ↦ ((pullbackCongr h).hom.app L).app ⊤ z)
    (pullGlobal_comp_hom r q L s)
  have he := hc.trans (SchemeModulePullbackUnits.congr_unit h L s)
  rw [pullbackStageIso_hom]
  exact he

end FLT.Mazur.FCurve
