/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianMarkings
public import FLT.Mazur.PolygonOriginalStageAdicSquare

/-!
# The actual complete markings recover the original finite-stage markings

The original cartesian stage square identifies its labeled section with the
unique lift of the complete marking. The section square itself is cartesian,
so its original ideal is exactly the restriction of the complete section ideal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local irreducible] family originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The lift to the actual stage square is the original labeled finite-order section. -/
theorem completeCartesianMarking_originalStage (m : ℕ) (i : Fin n) :
    completeCartesianMarking K n h (baseToSeries K m)
      (originalStageToCompatibleProj K n h m) (family K m n h).hom
      (originalStageToCompatibleProj_isPullback K n h m) i = marking K m n h i := by
  symm
  apply completeCartesianMarking_unique
  · exact (baseToSeries_completeBaseMarking K n h i m).symm
  · exact marking_base K m n h i

/-- The original finite-stage section square is cartesian over its complete section. -/
theorem completeMarking_originalStage_isPullback (m : ℕ) (i : Fin n) :
    IsPullback (marking K m n h i) (baseToSeries K m)
      (originalStageToCompatibleProj K n h m) (completeBaseMarking K n h i) := by
  have hp : IsPullback (marking K m n h i ≫ (family K m n h).hom)
      (baseToSeries K m) (baseToSeries K m)
      (completeBaseMarking K n h i ≫ exactVeroneseProjToBase K n h) := by
    rw [marking_base, completeBaseMarking_toBase]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact hp.of_right (baseToSeries_completeBaseMarking K n h i m).symm
    (originalStageToCompatibleProj_isPullback K n h m).flip

/-- The original stage ideal is the actual restriction of the complete marking ideal. -/
theorem completeBaseMarking_ker_originalStage (m : ℕ) (i : Fin n) :
    (completeBaseMarking K n h i).ker.comap (originalStageToCompatibleProj K n h m) =
      (marking K m n h i).ker := by
  let _ := completeBaseMarking_isClosedImmersion K n h i
  let hp := completeMarking_originalStage_isPullback K n h m i
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

end FLT.Mazur.PolygonInfinitesimalStages
