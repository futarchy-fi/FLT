/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientMorphism

/-!
# The actual comparison with the complete coefficient pullback

The structural square constructs a proper comparison into the categorical
pullback. Each original stage is already the actual adic fiber of that target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The canonical comparison from the independently constructed model to the actual pullback. -/
def completeCoefficientComparison : exactVeroneseProj L n h ⟶
    pullback (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (PowerSeries.map f))) :=
  pullback.lift (completeCoefficientProjMap f n h) (exactVeroneseProjToBase L n h)
    (completeCoefficientProjMap_toBase f n h)

/-- The comparison retains the actual complete coefficient morphism. -/
@[reassoc]
theorem completeCoefficientComparison_fst :
    completeCoefficientComparison f n h ≫ pullback.fst _ _ = completeCoefficientProjMap f n h :=
  pullback.lift_fst _ _ _

/-- The comparison retains the original structure map over the new complete base. -/
@[reassoc]
theorem completeCoefficientComparison_snd :
    completeCoefficientComparison f n h ≫ pullback.snd _ _ = exactVeroneseProjToBase L n h :=
  pullback.lift_snd _ _ _

/-- The actual comparison to the categorical coefficient pullback is proper. -/
theorem completeCoefficientComparison_isProper :
    IsProper (completeCoefficientComparison f n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := exactVeroneseProjToBase_isProper L n h
  let _ : IsProper (completeCoefficientComparison f n h ≫ pullback.snd _ _) := by
    rw [completeCoefficientComparison_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd _ _)

/-- Each original stage is the actual adic fiber of the coefficient pullback target. -/
theorem originalStageToCoefficientPullback_isPullback (m : ℕ) :
    IsPullback (originalStageToCompatibleProj L n h m ≫ completeCoefficientComparison f n h)
      (family L m n h).hom (pullback.snd _ _) (baseToSeries L m) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _)
    (h₂₂ := Spec.map (CommRingCat.ofHom (PowerSeries.map f)))
    ?_ ?_ (IsPullback.of_hasPullback _ _)
  · rw [Category.assoc, completeCoefficientComparison_fst,
      originalStageToCompatibleProj_coefficient, ← stageCoefficientBase_toSeries]
    exact (stageCoefficientFamily_isPullback f m n h).paste_horiz
      (originalStageToCompatibleProj_isPullback K n h m)
  · rw [Category.assoc, completeCoefficientComparison_snd,
      originalStageToCompatibleProj_toBase]

end FLT.Mazur.PolygonInfinitesimalStages
