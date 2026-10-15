/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affine section lifts for an immersion in its original target

Affine opens of the canonical closed-in-open neighborhood are transported
back to the original target. On these opens the original section map is
surjective, and its inverse-image open is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ImmersionAffineLifts
variable {X Y : Scheme} (f : X ⟶ Y) [IsImmersion f]
variable (U : f.coborderRange.toScheme.affineOpens)

/-- An affine open in the original target, retaining the actual open inclusion. -/
def target : Y.affineOpens :=
  ⟨f.coborderRange.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩

/-- Its full inverse image is affine because the factor in the neighborhood is closed. -/
def source : X.affineOpens :=
  ⟨f.liftCoborder ⁻¹ᵁ U.1, U.2.preimage f.liftCoborder⟩

/-- Transport keeps precisely the original inverse-image open. -/
theorem source_eq : (source f U).1 = f ⁻¹ᵁ (target f U).1 :=
  f.liftCoborder_preimage U.1

/-- The original map on sections, with its target expressed by the closed factorization. -/
theorem appLE_eq :
    f.appLE (target f U) (source f U) (le_of_eq (source_eq f U)) =
      f.liftCoborder.app U := by
  rw [liftCoborder_app]
  rfl

/-- Every section over the full inverse image lifts to the original affine target open. -/
theorem sections_surjective :
    Function.Surjective (f.appLE (target f U) (source f U) (le_of_eq (source_eq f U))) := by
  rw [appLE_eq]
  exact f.liftCoborder.app_surjective U.1 U.2

/-- These section-surjective affine patches cover the entire original source. -/
theorem exists_patch (x : X) :
    ∃ U : f.coborderRange.toScheme.affineOpens, x ∈ (source f U).1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    f.coborderRange.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.liftCoborder x)) TopologicalSpace.isOpen_univ
  exact ⟨⟨U, hU⟩, hx⟩

end FLT.Mazur.ImmersionAffineLifts
