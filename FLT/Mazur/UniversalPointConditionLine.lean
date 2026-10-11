/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalPointCondition
public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.CartierTensorRank

/-!
# Spreading a line with one full point condition

Tensoring the original line with the universal point ideal produces an actual
line over the curve parameter space. Its restriction is the original ideal
condition on every specified cartesian test, with no reducedness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor

variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules)

/-- The actual line obtained by imposing the universal point condition. -/
def universalPointConditionLine : (pullback f f).Modules :=
  tensor (idealModule (universalPointIdeal f)) ((Scheme.Modules.pullback (pullback.fst f f)).obj L)

/-- Point subtraction remains a line on the entire smooth parameter family. -/
theorem universalPointConditionLine_rankOne [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (hL : LocallyFreeRankOne L) :
    LocallyFreeRankOne (universalPointConditionLine f L) :=
  (universalPointIdeal_relativeCartier f).1.idealModule_locallyFreeRankOne.tensor
    (hL.pullback (pullback.fst f f))

variable [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {Y T : Scheme} {p : Y ⟶ X} {q : Y ⟶ T} {g : T ⟶ S}
  (H : IsPullback p q f g) (s : T ⟶ Y) (hs : s ≫ q = 𝟙 _)

/-- The full ideal module specializes along the specified family morphism. -/
def universalPointIdealModuleIso :
    (Scheme.Modules.pullback (pointConditionMap f H s hs)).obj
        (idealModule (universalPointIdeal f)) ≅ idealModule s.ker := by
  let _ := relativeCartierIdealPullback_originalSquare
    (pointConditionMap_isPullback f H s hs) _ (universalPointIdeal_relativeCartier f)
  exact asIso (idealModulePullbackHom _ _) ≪≫
    eqToIso (congrArg idealModule (universalPointIdeal_comap f H s hs))

/-- The spread line pulls back to precisely the original point-subtracted line. -/
def universalPointConditionLineIso :
    (Scheme.Modules.pullback (pointConditionMap f H s hs)).obj
        (universalPointConditionLine f L) ≅
      tensor (idealModule s.ker) ((Scheme.Modules.pullback p).obj L) :=
  ModuleLineBundleTensorPullback.tensorIso _ _ _ ≪≫
    congr (universalPointIdealModuleIso f H s hs)
      ((Scheme.Modules.pullbackComp (pointConditionMap f H s hs)
        (pullback.fst f f)).app L ≪≫
        eqToIso (congrArg (fun a ↦ (Scheme.Modules.pullback a).obj L)
          (pointConditionMap_fst f H s hs)))

end FLT.Mazur.FCurve
