/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedLineTwist
public import FLT.Mazur.ClosedLineProjectionFormula
public import FLT.Mazur.AmpleAffinePullback

/-!
# Associated-graded line twists on the closed subscheme

The actual graded ideal coefficient descends to a coherent module on the
closed subscheme. Graded coefficients of line powers are its twists by
powers of the restricted line, followed by closed pushforward.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentIdealIntersection ModuleSheafTensor
open ModuleLineBundleTensorPullback

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- The actual ideal-graded coefficient is killed by the original ideal. -/
theorem idealGraded_idealKilled (n : ℕ) : IdealKilled I (idealGraded I n) := by
  have := structureModule_coherent (X := X)
  exact (graded_idealKilled I (structureModule X) n).of_iso
    (gradedLineTwistIso I (structureModule X) structureModule_locallyFreeRankOne n ≪≫
      rightUnitor (idealGraded I n))

/-- The coherent graded ideal coefficient on the actual closed subscheme. -/
def closedIdealGraded (n : ℕ) : I.subscheme.Modules :=
  GlobalClosedModuleDescent.descent I (idealGraded I n) (idealGraded_idealKilled I n)

instance closedIdealGraded_coherent (n : ℕ) :
    (closedIdealGraded I n).IsFinitePresentation :=
  GlobalClosedModuleDescent.descent_isFinitePresentation I (idealGraded I n)
    (idealGraded_idealKilled I n)

/-- Closed pushforward recovers the original graded ideal coefficient. -/
def closedIdealGradedIso (n : ℕ) :
    (pushforward I.subschemeι).obj (closedIdealGraded I n) ≅ idealGraded I n :=
  GlobalClosedModuleDescent.pushforwardIso I (idealGraded I n) (idealGraded_idealKilled I n)

variable (L : X.Modules) [L.IsFinitePresentation] (hL : LocallyFreeRankOne L)

local instance power_coherent (d : ℕ) : (tensorPower L d).IsFinitePresentation := by
  induction d with
  | zero => exact structureModule_coherent
  | succ d hd =>
    have := hd
    exact GlobalIdealPower.tensor_coherent L (tensorPower L d)

/-- A graded line coefficient is the closed pushforward of its restricted twist. -/
def gradedClosedTwistIso (n : ℕ) :
    graded I L n ≅ (pushforward I.subschemeι).obj
      (tensor (closedIdealGraded I n) ((Scheme.Modules.pullback I.subschemeι).obj L)) :=
  gradedLineTwistIso I L hL n ≪≫
    ModuleSheafTensor.congr (closedIdealGradedIso I n).symm (Iso.refl L) ≪≫
      (ClosedLineProjectionFormula.projectionIso I.subschemeι (closedIdealGraded I n) L hL).symm

/-- The comparison for powers retains the actual closed restriction of the line. -/
def gradedPowerClosedTwistIso (d n : ℕ) :
    graded I (tensorPower L d) n ≅ (pushforward I.subschemeι).obj
      (tensor (closedIdealGraded I n)
        (tensorPower ((Scheme.Modules.pullback I.subschemeι).obj L) d)) := by
  exact gradedClosedTwistIso I (tensorPower L d) (hL.tensorPower d) n ≪≫
    (pushforward I.subschemeι).mapIso
      (ModuleSheafTensor.congr (Iso.refl _) (tensorPowerIso I.subschemeι L d))

end FLT.Mazur.IdealAdicQuotient
