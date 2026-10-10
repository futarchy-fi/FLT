/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiberBaseChange

/-!
# Ample fiber lines after a base isomorphism

Replacing an affine base by its spectrum preserves ampleness on the
corresponding fiber, with the line still on the unchanged total space.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

/-- A base isomorphism preserves ampleness of the actual fiber restriction. -/
theorem ampleLineBundle_fiber_baseIso {X S T : Scheme.{u}} (f : X ⟶ S)
    (e : S ≅ T) (s : S) (L : X.Modules)
    (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    AmpleLineBundle ((pullback ((f ≫ e.hom).fiberι (e.hom s))).obj L) := by
  have h : IsPullback (𝟙 X) (f ≫ e.hom) f e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hs : e.inv (e.hom s) = s := by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  have ha := ampleLineBundle_fiber_of_isPullback h (e.hom s) L (by rw [hs]; exact hL)
  exact ha.of_iso (((pullback ((f ≫ e.hom).fiberι (e.hom s))).mapIso
    ((pullbackId X).app L)).symm)

end FLT.Mazur.FCurve
