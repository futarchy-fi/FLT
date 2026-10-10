/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingBaseChange

/-!
# The inverse pullback adjunction retains actual projections

Returning a group-valued point from a base-changed group to the original
group is the first projection of its underlying scheme map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GroupMarkingBaseChange

universe u
variable {S T : Scheme.{u}} (g : T ⟶ S) (G : Over S) [MonObj G] (U : Over T)

/-- The inverse group-valued adjunction is the original first projection on scheme maps. -/
theorem pointsMulEquiv_symm_left (p : U ⟶ (Over.pullback g).obj G) :
    ((pointsMulEquiv g G U).symm p).left = p.left ≫ pullback.fst G.hom g := by
  have h := pointsMulEquiv_fst g G U ((pointsMulEquiv g G U).symm p)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

end FLT.Mazur.GroupMarkingBaseChange
