/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafBidualPullback
public import FLT.Mazur.LineSheafBidual
public import FLT.Mazur.ModuleSheafDualPullbackRestrict

/-!
# Inverse line biduality under base change

The canonical dual pullback isomorphisms normalize the original pulled
inverse bidual map to inverse biduality of the original pulled source line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} (hM : LocallyFreeRankOne M)

/-- The two canonical isomorphisms from a pulled line to its pulled dual's dual agree. -/
lemma lineBidual_pullback_iso :
    (pullback f).mapIso (lineSheafBidualIso hM) ≪≫ moduleSheafDualPullbackIso f hM.dual =
      lineSheafBidualIso (hM.pullback f) ≪≫
        moduleSheafDualIso _ (moduleSheafDualPullbackIso f hM) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, Functor.mapIso_hom, lineSheafBidualIso, asIso_hom,
    moduleSheafDualPullbackIso_hom, moduleSheafDualIso]
    using moduleSheafBidual_pullback f M

/-- Pulling inverse biduality keeps the original dual comparison maps. -/
lemma lineBidual_pullback_inv :
    (moduleSheafDualPullbackIso f hM.dual).inv ≫
        (pullback f).map (lineSheafBidualIso hM).inv =
      (moduleSheafDualIso _ (moduleSheafDualPullbackIso f hM)).inv ≫
        (lineSheafBidualIso (hM.pullback f)).inv := by
  have he := congrArg Iso.inv (lineBidual_pullback_iso f hM)
  simpa only [Iso.trans_inv, Functor.mapIso_inv] using he

/-- Transporting the twisting dual normalizes the actual pulled inverse bidual map. -/
lemma lineBidual_pullback_inv_normalized :
    (moduleSheafDualIso _ (moduleSheafDualPullbackIso f hM)).hom ≫
        (moduleSheafDualPullbackIso f hM.dual).inv ≫
          (pullback f).map (lineSheafBidualIso hM).inv =
      (lineSheafBidualIso (hM.pullback f)).inv := by
  rw [lineBidual_pullback_inv, Iso.hom_inv_id_assoc]

end FLT.Mazur.FCurve
