/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiberAffineOpenBaseChange

/-!
# Affine fiber opens after replacing the base by an isomorphic scheme

This specializes arbitrary base change to an isomorphism without changing
the total space or its generator opens.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.Approximation

/-- Replacing the base by an isomorphic scheme preserves affine fiber opens. -/
theorem isAffineOpen_fiber_preimage_baseIso {X S T : Scheme.{u}}
    (f : X ⟶ S) (e : S ≅ T) (s : S) (U : X.Opens)
    (hU : IsAffineOpen (f.fiberι s ⁻¹ᵁ U)) :
    IsAffineOpen ((f ≫ e.hom).fiberι (e.hom s) ⁻¹ᵁ U) := by
  have h : IsPullback (𝟙 X) (f ≫ e.hom) f e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hs : e.inv (e.hom s) = s := by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  have ha := isAffineOpen_fiber_preimage_of_isPullback h (e.hom s) U (by rw [hs]; exact hU)
  simpa using ha

end FLT.Mazur.Approximation
