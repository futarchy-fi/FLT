/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionOpenNeighborhood

/-!
# Exact section kernels on refined closed-in-open patches

When the entire closed inverse image belongs to the original open immersion,
its section map is an isomorphism. The composite therefore retains the
literal closed-immersion kernel, with no radical or saturation operation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ClosedImmersionOpenNeighborhood
variable {X Y Z : Scheme} (j : X ⟶ Y) (f : Y ⟶ Z)
  [IsOpenImmersion j] [IsClosedImmersion f]

omit [IsClosedImmersion f] in
/-- Restricting the closed subscheme to an open that contains it loses no equations. -/
theorem app_kernel (W : Z.Opens) (hW : f ⁻¹ᵁ W ≤ j.opensRange) :
    RingHom.ker ((j ≫ f).app W).hom = RingHom.ker (f.app W).hom := by
  let _ := j.isIso_app (f ⁻¹ᵁ W) hW
  rw [Scheme.Hom.comp_app]
  exact RingHom.ker_comp_of_injective (f.app W).hom
    ((ConcreteCategory.bijective_of_isIso (j.app (f ⁻¹ᵁ W))).injective)

/-- Transporting the full inverse image to the coborder patch preserves the kernel. -/
theorem patch_kernel (U : (j ≫ f).coborderRange.toScheme.affineOpens)
    (hU : (ImmersionAffineLifts.target (j ≫ f) U).1 ≤ neighborhood j f) :
    RingHom.ker ((j ≫ f).appLE (ImmersionAffineLifts.target (j ≫ f) U)
      (ImmersionAffineLifts.source (j ≫ f) U)
      (le_of_eq (ImmersionAffineLifts.source_eq (j ≫ f) U))).hom =
        RingHom.ker (f.app (ImmersionAffineLifts.target (j ≫ f) U)).hom := by
  rw [ImmersionAffineLifts.appLE_eq, liftCoborder_app]
  exact (RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom ((j ≫ f).liftCoborder_preimage U.1)).op)).injective).trans
        (app_kernel j f _ (preimage_le_range j f _ hU))

end FLT.Mazur.ClosedImmersionOpenNeighborhood
