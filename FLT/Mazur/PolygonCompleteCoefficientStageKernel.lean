/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalBaseAdicKernel
public import FLT.Mazur.PolygonCompleteCoefficientPullback

/-!
# Actual adic ideals on the complete coefficient pullback

The original stage maps into the actual coefficient pullback are closed
immersions with exactly the extended parameter-power ideals.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage is a closed subscheme of the actual coefficient pullback. -/
theorem originalStageToCoefficientPullback_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (originalStageToCompatibleProj L n h m ≫
      completeCoefficientComparison f n h) := by
  let _ := baseToSeries_isClosedImmersion L m
  rw [← (originalStageToCoefficientPullback_isPullback f n h m).isoPullback_hom_fst]
  infer_instance

/-- Its defining ideal is the actual base parameter ideal raised to the original power. -/
theorem originalStageToCoefficientPullback_ker (m : ℕ) :
    (originalStageToCompatibleProj L n h m ≫ completeCoefficientComparison f n h).ker =
      (BaseAdicThickening.baseIdeal (.of (PowerSeries L)) (parameterIdeal L)).comap
        (pullback.snd (exactVeroneseProjToBase K n h)
          (Spec.map (CommRingCat.ofHom (PowerSeries.map f)))) ^ (m + 1) := by
  let _ := baseToSeries_isClosedImmersion L m
  rw [← (originalStageToCoefficientPullback_isPullback f n h m).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    baseToSeries_ker, idealSheaf_comap_pow]

end FLT.Mazur.PolygonInfinitesimalStages
