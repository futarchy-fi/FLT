/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientIsomorphism
public import FLT.Mazur.PolygonCompleteCoefficientMarkings

/-!
# The global coefficient isomorphism retains the original marked family

Both projections are the original constructed maps. The inverse recovers
every original labeled marking and every original infinitesimal stage map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj completeBaseMarking
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The coefficient isomorphism retains the previously constructed first projection. -/
@[reassoc]
theorem completeCoefficientPullbackIso_fst :
    (completeCoefficientPullbackIso f n h).hom ≫ pullback.fst _ _ =
      completeCoefficientProjMap f n h :=
  completeCoefficientComparison_fst f n h

/-- The coefficient isomorphism retains the independently constructed structure map. -/
@[reassoc]
theorem completeCoefficientPullbackIso_snd :
    (completeCoefficientPullbackIso f n h).hom ≫ pullback.snd _ _ =
      exactVeroneseProjToBase L n h :=
  completeCoefficientComparison_snd f n h

/-- Each original labeled marking is carried to its actual pullback section. -/
@[reassoc]
theorem completeBaseMarking_coefficientPullbackIso (i : Fin n) :
    completeBaseMarking L n h i ≫ (completeCoefficientPullbackIso f n h).hom =
      completeFiberMarking K n h (Spec.map (CommRingCat.ofHom (PowerSeries.map f))) i :=
  completeBaseMarking_coefficientComparison f n h i

/-- The recovered global inverse returns every original marking with its label intact. -/
@[reassoc]
theorem completeFiberMarking_coefficientPullbackIso_inv (i : Fin n) :
    completeFiberMarking K n h (Spec.map (CommRingCat.ofHom (PowerSeries.map f))) i ≫
      (completeCoefficientPullbackIso f n h).inv = completeBaseMarking L n h i := by
  rw [← completeBaseMarking_coefficientPullbackIso f n h i, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The inverse retains each original stage's full morphism into the complete family. -/
@[reassoc]
theorem originalStage_coefficientPullbackIso_inv (m : ℕ) :
    (originalStageToCompatibleProj L n h m ≫ completeCoefficientComparison f n h) ≫
      (completeCoefficientPullbackIso f n h).inv = originalStageToCompatibleProj L n h m := by
  change (_ ≫ (completeCoefficientPullbackIso f n h).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
