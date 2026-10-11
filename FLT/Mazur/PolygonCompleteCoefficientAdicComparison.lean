/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientPullback

/-!
# The complete coefficient comparison is an isomorphism on every actual stage

Both complete models have the same original finite-stage fibers. Cancellation
of their cartesian structural squares makes the comparison the identity there.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Pulling back the actual comparison to any original stage gives its identity map. -/
theorem completeCoefficientComparison_stage_isPullback (m : ℕ) :
    IsPullback (𝟙 (family L m n h).left) (originalStageToCompatibleProj L n h m)
      (originalStageToCompatibleProj L n h m ≫ completeCoefficientComparison f n h)
      (completeCoefficientComparison f n h) := by
  apply IsPullback.of_right (h₁₂ := (family L m n h).hom)
    (h₂₂ := pullback.snd _ _) ?_ (by simp)
    (originalStageToCoefficientPullback_isPullback f n h m).flip
  simpa only [Category.id_comp, completeCoefficientComparison_snd] using
    (originalStageToCompatibleProj_isPullback L n h m).flip

/-- The stage's canonical map to the comparison fiber product is an actual isomorphism. -/
def completeCoefficientComparisonStageIso (m : ℕ) :
    (family L m n h).left ≅
      pullback (originalStageToCompatibleProj L n h m ≫ completeCoefficientComparison f n h)
        (completeCoefficientComparison f n h) :=
  (completeCoefficientComparison_stage_isPullback f n h m).isoPullback

/-- The constructed fiber-product isomorphism retains the identity of the original stage. -/
@[reassoc]
theorem completeCoefficientComparisonStageIso_fst (m : ℕ) :
    (completeCoefficientComparisonStageIso f n h m).hom ≫ pullback.fst _ _ = 𝟙 _ :=
  (completeCoefficientComparison_stage_isPullback f n h m).isoPullback_hom_fst

/-- Its other projection is the original stage map of the independently constructed model. -/
@[reassoc]
theorem completeCoefficientComparisonStageIso_snd (m : ℕ) :
    (completeCoefficientComparisonStageIso f n h m).hom ≫ pullback.snd _ _ =
      originalStageToCompatibleProj L n h m :=
  (completeCoefficientComparison_stage_isPullback f n h m).isoPullback_hom_snd

end FLT.Mazur.PolygonInfinitesimalStages
