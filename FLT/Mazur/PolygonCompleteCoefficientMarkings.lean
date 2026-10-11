/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientPullback
public import FLT.Mazur.PolygonCompleteFiberMarkings
public import FLT.Mazur.PowerSeriesSchemePointExt

/-!
# Complete coefficient comparison retains the original labels

The actual finite-stage coefficient equations determine every complete marking.
The canonical comparison therefore preserves the original pullback markings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj completeBaseMarking
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete coefficient map retains every individually labeled original marking. -/
@[reassoc]
theorem completeBaseMarking_coefficient (i : Fin n) :
    completeBaseMarking L n h i ≫ completeCoefficientProjMap f n h =
      Spec.map (CommRingCat.ofHom (PowerSeries.map f)) ≫ completeBaseMarking K n h i := by
  apply powerSeriesPoint_ext L
  intro m
  rw [baseToSeries_completeBaseMarking_assoc,
    originalStageToCompatibleProj_coefficient,
    ← Category.assoc, marking_stageCoefficientFamily, Category.assoc,
    ← baseToSeries_completeBaseMarking, ← Category.assoc, stageCoefficientBase_toSeries,
    Category.assoc]

/-- The comparison with the actual pullback retains its original labeled sections. -/
@[reassoc]
theorem completeBaseMarking_coefficientComparison (i : Fin n) :
    completeBaseMarking L n h i ≫ completeCoefficientComparison f n h =
      completeFiberMarking K n h (Spec.map (CommRingCat.ofHom (PowerSeries.map f))) i := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeCoefficientComparison_fst,
      completeBaseMarking_coefficient, completeFiberMarking_fst]
  · rw [Category.assoc, completeCoefficientComparison_snd,
      completeBaseMarking_toBase, completeFiberMarking_snd]

end FLT.Mazur.PolygonInfinitesimalStages
