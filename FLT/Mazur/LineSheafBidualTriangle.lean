/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafBidual

/-!
# The intrinsic bidual triangle

Evaluation proves that dualizing biduality retracts biduality of the dual.
For a line this identifies the inverse bidual map without choosing a frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor moduleSheafBidual
  moduleSheafDualMap moduleSheafDualEvaluation
variable {X : Scheme.{u}}

private lemma bidual_triangle_eval (M : X.Modules) (U : X.Opens)
    (φ : Γ(moduleSheafDual M, U)) (s : Γ(M, U)) :
    moduleDualEval M U
      ((moduleSheafDualMap M (moduleSheafBidual M)).app U
        ((moduleSheafBidual (moduleSheafDual M)).app U φ)) s =
      moduleDualEval M U φ s := by
  rw [moduleSheafDualMap_app, moduleDualEval_precomp,
    moduleSheafBidual_eval, moduleSheafBidual_eval]

/-- Evaluation-defined biduality satisfies the original dual triangle. -/
lemma moduleSheafBidual_triangle (M : X.Modules) :
    moduleSheafBidual (moduleSheafDual M) ≫ moduleSheafDualMap M (moduleSheafBidual M) =
      𝟙 (moduleSheafDual M) := by
  apply moduleSheafDual_hom_ext M (moduleSheafDual M)
  apply ModuleSheafTensor.hom_ext
  intro U φ s
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure] using
      bidual_triangle_eval M U φ s

/-- The inverse bidual map of a line's dual is the dual of its original bidual map. -/
lemma lineSheafBidual_dual_inv {M : X.Modules} (hM : LocallyFreeRankOne M) :
    (lineSheafBidualIso hM.dual).inv = moduleSheafDualMap M (lineSheafBidualIso hM).hom := by
  apply (cancel_epi (lineSheafBidualIso hM.dual).hom).mp
  rw [Iso.hom_inv_id]
  exact (moduleSheafBidual_triangle M).symm

end FLT.Mazur.FCurve
