/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapCover

/-!
# Named projections from the relative overlap

Explicit source types retain the pullback instance already selected by
the named overlap, avoiding fresh instance choices in coefficient comparisons.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The first projection with the named overlap as its explicit source. -/
def relativeOverlapFirstProjection (U V : X.affineOpens) :
    relativeTensorOverlap J f U V ⟶ Spec (.of (RelativeAlgebra J f U)) :=
  Limits.pullback.fst _ _

/-- The second projection with the named overlap as its explicit source. -/
def relativeOverlapSecondProjection (U V : X.affineOpens) :
    relativeTensorOverlap J f U V ⟶ Spec (.of (RelativeAlgebra J f V)) :=
  Limits.pullback.snd _ _

/-- The first named projection restricts to the original tensor transition. -/
lemma relativeOverlapFirstProjection_chart {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeTensorOverlapChart J f i j ≫ relativeOverlapFirstProjection J f U V =
      relativeTensorTransition J f i := relativeTensorOverlapChart_fst J f i j

/-- The second named projection restricts to the original tensor transition. -/
lemma relativeOverlapSecondProjection_chart {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeTensorOverlapChart J f i j ≫ relativeOverlapSecondProjection J f U V =
      relativeTensorTransition J f j := relativeTensorOverlapChart_snd J f i j

end FLT.Mazur.IdealAdicGradedPullback
