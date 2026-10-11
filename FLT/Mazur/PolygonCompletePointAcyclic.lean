/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedPointAcyclic
public import FLT.Mazur.PolygonCompleteLineCohomology
public import FLT.Mazur.AcyclicCoefficientCohomology

/-!
# Positive point powers on the complete family and its actual affine squares

Closed acyclicity transfers to the complete family through the regular
parameter quotient. The flat-family Cech comparison then proves vanishing
on every affine base change, including the original generic fiber.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original complete single-point coefficient is locally free of rank one. -/
theorem completePointLine_locallyFreeRankOne (i : Fin n) :
    LocallyFreeRankOne (completePointLine K n h i) :=
  (completeBaseMarking_relativeCartier K n h i).1.divisorLineBundle_locallyFreeRankOne

/-- Every positive point power on the actual complete family is positive-acyclic. -/
theorem completePointPower_positive (i : Fin n) (m r : ℕ) :
    Subsingleton (ModuleH (tensorPower (completePointLine K n h i) (m + 1)) (r + 1)) :=
  completeLine_vanishing_of_closed K n h _
    ((completePointLine_locallyFreeRankOne K n h i).tensorPower (m + 1)) (r + 1)
      (completePointPower_closed_positive K n h i m r)

variable {S Y : Scheme} [IsAffine S] (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

include hs in
/-- Vanishing survives every actual affine base change of the original point power. -/
theorem completePointPower_affine_positive (i : Fin n) (m r : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback p).obj
      (tensorPower (completePointLine K n h i) (m + 1))) (r + 1)) := by
  let _ : (exactVeroneseProj K n h).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))).IsSeparated
  let _ := exactVeroneseProjToBase_flat K n h
  exact LineSectionBaseChange.acyclic_pullback_positive hs _
    ((completePointLine_locallyFreeRankOne K n h i).tensorPower (m + 1))
    (completePointPower_positive K n h i m) r

include hs in
/-- The actual retained Cartesian point coefficient has the same universal vanishing. -/
theorem completeCartesianPointPower_affine_positive (i : Fin n) (m r : ℕ) :
    Subsingleton (ModuleH
      (tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1)) (r + 1)) := by
  let _ := completePointPower_affine_positive K n h s p q hs i m r
  exact moduleH_subsingleton_of_iso
    (completeCartesianPointPowerIso K n h s p q hs i (m + 1)).symm (r + 1)

end FLT.Mazur.PolygonInfinitesimalStages
