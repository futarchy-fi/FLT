/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAffineFppfDescent

/-!
# Global fppf descent of effective Cartier ideals

Restrict to affine opens of the target, refine the fppf map by a finite
affine faithfully flat map, descend finite presentation, and spread the
regular ideal stalk generators. No Cartier-chart assumption is imposed on
the ideal downstairs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- An effective Cartier ideal descends along a flat surjective morphism
locally of finite presentation. -/
theorem effectiveCartier_of_fppf_comap (I : Y.IdealSheafData) (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    (hI : EffectiveCartier (I.comap f)) : EffectiveCartier I := by
  apply (effectiveCartier_iff_affine_restrict I).mpr
  intro U
  let g := pullback.snd f U.1.ι
  apply effectiveCartier_of_flat_surjective_open_affine (I.comap U.1.ι) g g.isOpenMap
  have h := hI.comap_of_isOpenImmersion (pullback.fst f U.1.ι)
  rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
    Scheme.IdealSheafData.comap_comp] at h
  exact h

end FLT.Mazur.FCurve
