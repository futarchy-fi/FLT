/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAffineOverlap
public import FLT.Mazur.IdealAdicRelativeOverlapCover
public import FLT.Mazur.SheafPullbackLocalComparison

/-!
# Local coefficient comparisons on the full relative overlap

On each common affine chart, the pullbacks of the two coefficient sheaves
from the full overlap are canonically isomorphic. Their original affine
normalization is retained. Compatibility after further refinement is a
separate descent step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeRestriction relativeMap relativeCoefficientSheafMap
attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] relativeTensorTransition relativeTensorOverlapChart
attribute [local irreducible] relativeTensorChart relativeChartCoefficientSheaf
attribute [local irreducible] relativeCoefficientAffineOverlap

/-- The coefficient sheaf pulled back from the first chart to the full overlap. -/
def relativeOverlapLeftCoefficient (U V : X.affineOpens) :
    (relativeTensorOverlap J f U V).Modules :=
  (pullback (Limits.pullback.fst (relativeTensorChart J f U)
    (relativeTensorChart J f V))).obj (relativeChartCoefficientSheaf J f U)

/-- The coefficient sheaf pulled back from the second chart to the full overlap. -/
def relativeOverlapRightCoefficient (U V : X.affineOpens) :
    (relativeTensorOverlap J f U V).Modules :=
  (pullback (Limits.pullback.snd (relativeTensorChart J f U)
    (relativeTensorChart J f V))).obj (relativeChartCoefficientSheaf J f V)

/-- The affine coefficient comparison expressed on restrictions of the overlap sheaves. -/
def relativeOverlapCoefficientChartMap {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (pullback (relativeTensorOverlapChart J f i j)).obj
        (relativeOverlapLeftCoefficient J f U V) ⟶
      (pullback (relativeTensorOverlapChart J f i j)).obj
        (relativeOverlapRightCoefficient J f U V) :=
  SheafPullbackLocalComparison.transport (relativeTensorOverlapChart J f i j)
    (Limits.pullback.fst _ _) (Limits.pullback.snd _ _)
    (relativeTensorTransition J f i) (relativeTensorTransition J f j)
    (relativeTensorOverlapChart_fst J f i j) (relativeTensorOverlapChart_snd J f i j)
    (relativeChartCoefficientSheaf J f U) (relativeChartCoefficientSheaf J f V)
    (relativeCoefficientAffineOverlap J f i j).hom

/-- The local map between the full overlap restrictions is invertible. -/
instance relativeOverlapCoefficientChartMap_isIso {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    IsIso (relativeOverlapCoefficientChartMap J f i j) := by
  unfold relativeOverlapCoefficientChartMap
  infer_instance

/-- Normalization gives exactly the previously proved original affine comparison. -/
lemma relativeOverlapCoefficientChartMap_normalize {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeOverlapCoefficientChartMap J f i j ≫
        (SheafPullbackPathComparison.comparison (relativeTensorOverlapChart J f i j)
          (Limits.pullback.snd _ _) (relativeTensorTransition J f j)
          (relativeTensorOverlapChart_snd J f i j)).hom.app
            (relativeChartCoefficientSheaf J f V) =
      (SheafPullbackPathComparison.comparison (relativeTensorOverlapChart J f i j)
          (Limits.pullback.fst _ _) (relativeTensorTransition J f i)
          (relativeTensorOverlapChart_fst J f i j)).hom.app
            (relativeChartCoefficientSheaf J f U) ≫
        (relativeCoefficientAffineOverlap J f i j).hom :=
  SheafPullbackLocalComparison.transport_normalize _ _ _ _ _ _ _ _ _ _

end FLT.Mazur.IdealAdicGradedPullback
