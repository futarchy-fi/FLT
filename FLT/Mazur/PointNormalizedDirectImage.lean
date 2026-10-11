/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedLineBundle
public import FLT.Mazur.ClosedLineProjectionFormula
public import FLT.Mazur.LineTensorEquivalence

/-!
# Point normalization preserves the actual direct-image line condition

The line projection formula identifies the normalized direct image with
the original direct image tensored by the dual point restriction. Tensor
cancellation proves preservation and detection of local rank one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
attribute [local irreducible] ModuleSheafTensor.tensor

/-- Tensoring any sheaf with a line preserves and detects local rank one. -/
theorem locallyFreeRankOne_tensor_line_iff {X : Scheme.{u}} (M N : X.Modules)
    (hN : LocallyFreeRankOne N) :
    LocallyFreeRankOne (ModuleSheafTensor.tensor M N) ↔ LocallyFreeRankOne M := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.tensor hN⟩
  exact (h.tensor hN.dual).of_iso (tensorCancelIso M
    (ModuleSheafTensorAssociator.comm N (moduleSheafDual N) ≪≫ lineSheafDualEvaluationIso hN))

end FLT.Mazur.FCurve

namespace FLT.Mazur.SchemePicard
open FCurve
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The actual normalized direct image is the original direct image with the point dual twist. -/
@[irreducible] def pointNormalizedLineDirectImageIso :
    (Scheme.Modules.pushforward f).obj (pointNormalizedLine f e L) ≅
      ModuleSheafTensor.tensor ((Scheme.Modules.pushforward f).obj L)
        (moduleSheafDual ((Scheme.Modules.pullback e).obj L)) := by
  unfold pointNormalizedLine
  exact ClosedLineProjectionFormula.projectionIso f L _ (hL.pullback e).dual

include hL in
/-- Actual point normalization preserves and detects the direct-image line condition. -/
theorem pointNormalizedLine_directImage_rankOne_iff :
    LocallyFreeRankOne ((Scheme.Modules.pushforward f).obj (pointNormalizedLine f e L)) ↔
      LocallyFreeRankOne ((Scheme.Modules.pushforward f).obj L) := by
  have hi := pointNormalizedLineDirectImageIso f e L hL
  refine (show LocallyFreeRankOne ((Scheme.Modules.pushforward f).obj
      (pointNormalizedLine f e L)) ↔ LocallyFreeRankOne
        (ModuleSheafTensor.tensor ((Scheme.Modules.pushforward f).obj L)
          (moduleSheafDual ((Scheme.Modules.pullback e).obj L))) from
    ⟨fun h ↦ h.of_iso hi, fun h ↦ h.of_iso hi.symm⟩).trans ?_
  exact locallyFreeRankOne_tensor_line_iff _ _ (hL.pullback e).dual

end FLT.Mazur.SchemePicard
