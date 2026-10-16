/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionOpenNeighborhood

/-!
# Refined closed-immersion patches inside a prescribed ambient open

The full inverse image remains in the original open subscheme, while the
complete affine patch can also be required to lie in a chosen coordinate chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ClosedImmersionOpenNeighborhood
variable {X Y Z : Scheme} (j : X ⟶ Y) (f : Y ⟶ Z)
  [IsOpenImmersion j] [IsClosedImmersion f]

/-- Refine around an original point inside any prescribed complete ambient neighborhood. -/
theorem exists_refined_patch_in (x : X) (W : Z.Opens) (hx : (j ≫ f) x ∈ W) :
    ∃ U : (j ≫ f).coborderRange.toScheme.affineOpens,
      x ∈ (ImmersionAffineLifts.source (j ≫ f) U).1 ∧
      (ImmersionAffineLifts.target (j ≫ f) U).1 ≤ W ∧
      (ImmersionAffineLifts.target (j ≫ f) U).1 ≤ neighborhood j f := by
  let V := (j ≫ f).coborderRange.ι ⁻¹ᵁ W
  have hv : (j ≫ f).liftCoborder x ∈ V := by
    change ((j ≫ f).liftCoborder ≫ (j ≫ f).coborderRange.ι) x ∈ W
    rwa [Scheme.Hom.liftCoborder_ι]
  obtain ⟨U, hu, hUV, hN⟩ := exists_refined_patch j f x V hv
  refine ⟨U, hu, ?_, hN⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hUV hy

end FLT.Mazur.ClosedImmersionOpenNeighborhood
