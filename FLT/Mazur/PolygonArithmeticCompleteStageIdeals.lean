/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticFamilyFlatness
public import FLT.Mazur.PolygonArithmeticOriginalAdicSquare

/-!
# The actual complete markings recover the original finite-stage markings

The original cartesian stage square identifies its labeled section with the
unique lift of the complete marking. The section square itself is cartesian,
so its original ideal is exactly the restriction of the complete section ideal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local irreducible] family originalStageToCompatibleProj

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original finite-stage section square is cartesian over its complete section. -/
theorem completeMarking_originalStage_isPullback (m : ℕ) (i : Fin n) :
    IsPullback (marking A π m n h i) (baseToIntegral A π m)
      (originalStageToCompatibleProj A π hne hgen n h m)
      (completeBaseMarking A π hne hgen n h i) := by
  have hp : IsPullback (marking A π m n h i ≫ (family A π m n h).hom)
      (baseToIntegral A π m) (baseToIntegral A π m)
      (completeBaseMarking A π hne hgen n h i ≫ exactVeroneseProjToBase A π n h hne hgen) := by
    rw [marking_base, completeBaseMarking_toBase]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact hp.of_right (baseToIntegral_completeBaseMarking A π hne hgen n h i m).symm
    (originalStageToCompatibleProj_isPullback A π hne hgen n h m).flip

/-- The original stage ideal is the actual restriction of the complete marking ideal. -/
theorem completeBaseMarking_ker_originalStage (m : ℕ) (i : Fin n) :
    (completeBaseMarking A π hne hgen n h i).ker.comap
      (originalStageToCompatibleProj A π hne hgen n h m) =
      (marking A π m n h i).ker := by
  let _ := completeBaseMarking_isClosedImmersion A π hne hgen n h i
  let hp := completeMarking_originalStage_isPullback A π hne hgen n h m i
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

end FLT.Mazur.PolygonArithmeticStages
