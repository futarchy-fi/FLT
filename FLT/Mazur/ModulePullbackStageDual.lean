/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackStageIso
public import FLT.Mazur.DualPullbackComposition
public import FLT.Mazur.ModuleSheafDualPullbackRestrict

/-!
# Canonical duality and original stage comparisons

The sealed stage isomorphism commutes with canonical pullback of line duals.
The dual of the stage comparison is contravariant, hence its inverse occurs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p) {L : S.Modules} (hL : LocallyFreeRankOne L)

/-- Dual pullback preserves the original stage comparison, including its contravariance. -/
theorem pullbackStageIso_dual :
    (pullback r).map (moduleSheafDualPullbackIso q hL).hom ≫
        (moduleSheafDualPullbackIso r (hL.pullback q)).hom ≫
          (moduleSheafDualIso _ (pullbackStageIso p q r h L)).inv =
      (pullbackStageIso p q r h (moduleSheafDual L)).hom ≫
        (moduleSheafDualPullbackIso p hL).hom := by
  subst p
  apply (cancel_mono (moduleSheafDualIso _ (pullbackStageIso (r ≫ q) q r rfl L)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [pullbackStageIso_hom, pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, moduleSheafDualIso,
    moduleSheafDualPullbackIso_hom]
  exact moduleSheafDualPullbackHom_comp r q L

end FLT.Mazur.FCurve
