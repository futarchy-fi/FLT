/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePullback

/-!
# Closed-subscheme factorization as vanishing of the pulled ideal map

The criterion uses the actual morphism from the pulled ideal module to the
structure sheaf. It works for arbitrary scheme maps, without reducedness or
quasi-compactness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual pulled ideal inclusion vanishes precisely when the ideal is killed. -/
theorem idealModulePullbackι_eq_zero_iff :
    idealModulePullbackι I f = 0 ↔ I ≤ f.ker := by
  constructor
  · intro h
    apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
    intro U x hx
    let s := (idealModuleAffineEquiv I U).symm ⟨x, hx⟩
    have hs : (idealModuleι I).app U.1 s = x := by
      rw [← idealModuleAffineEquiv_val]
      exact congrArg Subtype.val ((idealModuleAffineEquiv I U).apply_symm_apply ⟨x, hx⟩)
    have hz := idealModulePullbackι_unit I f U.1 s
    rw [h, hs] at hz
    exact hz.symm
  · intro h
    apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
    apply moduleHom_ext_affine
    intro U
    ext s
    change (idealModulePullbackι I f).app (f ⁻¹ᵁ U.1)
      (((pullbackPushforwardAdjunction f).unit.app _).app U.1 s) = 0
    rw [idealModulePullbackι_unit]
    apply f.ideal_ker_le U
    apply h U
    rw [← idealModuleAffineEquiv_val]
    exact (idealModuleAffineEquiv I U s).property

/-- Vanishing of the pulled ideal map is equivalently vanishing of its image ideal. -/
theorem idealModulePullbackι_eq_zero_iff_comap :
    idealModulePullbackι I f = 0 ↔ I.comap f = ⊥ := by
  rw [idealModulePullbackι_eq_zero_iff, ← Scheme.IdealSheafData.map_bot f,
    Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff]

/-- The zero equation represents factorization through the actual closed subscheme. -/
theorem idealModulePullbackι_eq_zero_iff_lift :
    idealModulePullbackι I f = 0 ↔ ∃ g : X ⟶ I.subscheme, g ≫ I.subschemeι = f := by
  rw [idealModulePullbackι_eq_zero_iff]
  constructor
  · intro h
    have hk : I.subschemeι.ker ≤ f.ker := by simpa using h
    exact ⟨IsClosedImmersion.lift I.subschemeι f hk,
      IsClosedImmersion.lift_fac I.subschemeι f hk⟩
  · rintro ⟨g, rfl⟩
    simpa using Scheme.Hom.le_ker_comp g I.subschemeι

end FLT.Mazur.FCurve
