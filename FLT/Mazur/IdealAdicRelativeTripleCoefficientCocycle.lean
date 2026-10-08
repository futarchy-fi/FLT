/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeTripleCoefficientNormalization

/-!
# The full triple-overlap coefficient cocycle

The global pair comparisons compose after transport to common coordinate
sheaves on the entire scheme-theoretic triple overlap.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open SheafPullbackPathComparison

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart relativeTensorChart
attribute [local irreducible] relativeChartCoefficientSheaf relativeCoefficientAffineOverlap
attribute [local irreducible] relativeOverlapCoefficientIso relativeTensorTripleOverlapChart
attribute [local irreducible] relativeTripleFirstCoefficientMap relativeTripleLastCoefficientMap
attribute [local irreducible] relativeTripleOuterCoefficientMap

/-- The normalized full-overlap coefficient isomorphisms satisfy the global cocycle. -/
theorem relativeTripleCoefficientMap_cocycle (U V T : X.affineOpens) :
    relativeTripleFirstCoefficientMap J f U V T ≫
        relativeTripleLastCoefficientMap J f U V T =
      relativeTripleOuterCoefficientMap J f U V T := by
  apply relativeTensorTripleOverlap_hom_ext J f U V T
  intro W i j k
  apply (cancel_mono ((comparison (relativeTensorTripleOverlapChart J f i j k)
    (relativeTripleThirdProjection J f U V T) (relativeTensorTransition J f k)
    (relativeTensorTripleOverlapChart_third J f i j k)).hom.app
      (relativeChartCoefficientSheaf J f T))).mp
  rw [Functor.map_comp, Category.assoc, relativeTripleLastCoefficientMap_chart,
    ← Category.assoc, relativeTripleFirstCoefficientMap_chart, Category.assoc,
    relativeOverlapCoefficientAffineMap_cocycle, relativeTripleOuterCoefficientMap_chart]

end FLT.Mazur.IdealAdicGradedPullback
