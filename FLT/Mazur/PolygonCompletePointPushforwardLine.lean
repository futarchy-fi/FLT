/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionRank
public import FLT.Mazur.ProperLinePushforwardTilde
public import FLT.Mazur.AffinePicardSections

/-!
# Rank-one direct image over the complete base

Affine reconstruction of the proved rank-one section module makes the actual
pushforward a line, retaining the original complete family and point divisor.
No smoothness or group structure of the total polygon is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The retained marking proves surjectivity of the original complete family. -/
theorem completePointFamily_surjective (i : Fin n) :
    Surjective (exactVeroneseProjToBase K n h) := by
  let _ : Surjective (completeBaseMarking K n h i ≫ exactVeroneseProjToBase K n h) := by
    rw [completeBaseMarking_toBase]
    infer_instance
  exact Surjective.of_comp (completeBaseMarking K n h i) _

/-- The degree-one power has an actual rank-one direct image over the complete base. -/
theorem completePointOne_pushforward_rankOne (i : Fin n) :
    LocallyFreeRankOne ((pushforward (exactVeroneseProjToBase K n h)).obj
      (tensorPower (completePointLine K n h i) 1)) := by
  let f := exactVeroneseProjToBase K n h
  let M := tensorPower (completePointLine K n h i) 1
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := ((completePointLine_locallyFreeRankOne K n h i).tensorPower 1).isFinitePresentation
  let _ := LineSectionBaseChange.properPushforward_isQuasicoherent f M
  let _ := (structureModule_locallyFreeRankOne
    (X := Spec (.of (PowerSeries K)))).isFinitePresentation
  let _ := completePointPower_sections_free K n h i 0
  let e := (Module.nonempty_linearEquiv_of_finrank_eq_one
    (completePointPower_sections_finrank K n h i 0)).some
  let a : (pushforward f).obj M ≅ structureModule (Spec (.of (PowerSeries K))) :=
    SchemePicard.isoOfSections
    ((LineSectionBaseChange.properPushforwardSectionsEquiv f M).trans e.symm)
  exact structureModule_locallyFreeRankOne.of_iso a.symm

/-- Removing the power unitor retains the original point-line direct image. -/
theorem completePointLine_pushforward_rankOne (i : Fin n) :
    LocallyFreeRankOne ((pushforward (exactVeroneseProjToBase K n h)).obj
      (completePointLine K n h i)) :=
  (completePointOne_pushforward_rankOne K n h i).of_iso
    ((pushforward (exactVeroneseProjToBase K n h)).mapIso
      (ModuleSheafTensor.rightUnitor (completePointLine K n h i)))

end FLT.Mazur.PolygonInfinitesimalStages
