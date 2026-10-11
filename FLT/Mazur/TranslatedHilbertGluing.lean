/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertSchemeCocycle
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Gluing the translated Hilbert parameter schemes

The proved overlaps and triple cocycle construct an actual scheme with open
Hilbert charts. This is the union of the specified translated charts; coverage
of the whole original Picard sheaf is a separate geometric question.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {ι : Type} (a : ι → TranslatedHilbertIndex f)

/-- Forgetting the base preserves the proved pullback cocycle and all open projections. -/
def translatedHilbertGlueData : Scheme.GlueData where
  J := ι
  U i := (acyclicHilbertTest f (a i).1).left
  V p := (translatedHilbertChartOverlap f hL (a p.1) (a p.2)).left
  f i j := (translatedHilbertChartOverlapLeft f hL (a i) (a j)).left
  f_id i := by
    change IsIso ((Over.forget _).map (translatedHilbertChartOverlapLeft f hL (a i) (a i)))
    infer_instance
  t i j := (translatedHilbertChartOverlapSwap f hL (a i) (a j)).left
  t_id i := congrArg Over.Hom.left (translatedHilbertOverlapSwap_self f hL (a i))
  t' i j k := translatedHilbertSchemeRotate f hL (a i) (a j) (a k)
  t_fac i j k := translatedHilbertSchemeRotate_snd f hL (a i) (a j) (a k)
  cocycle i j k := translatedHilbertSchemeRotate_cocycle f hL (a i) (a j) (a k)
  f_open i j := translatedHilbertChartOverlapLeft_isOpenImmersion f hL (a i) (a j)

/-- The scheme glued from the actual translated Hilbert parameter charts. -/
def translatedHilbertGlued : Scheme := (translatedHilbertGlueData f hL a).glued

/-- Inclusion of each original parameter scheme in the constructed glued scheme. -/
def translatedHilbertGluedChart (i : ι) :
    (acyclicHilbertTest f (a i).1).left ⟶ translatedHilbertGlued f hL a :=
  (translatedHilbertGlueData f hL a).ι i

instance translatedHilbertGluedChart_isOpenImmersion (i : ι) :
    IsOpenImmersion (translatedHilbertGluedChart f hL a i) :=
  (translatedHilbertGlueData f hL a).ι_isOpenImmersion i

/-- The translated charts form an actual open cover of their glued scheme. -/
def translatedHilbertGluedCover : (translatedHilbertGlued f hL a).OpenCover :=
  (translatedHilbertGlueData f hL a).openCover

/-- Every point of the glued scheme lies in one of the unchanged parameter charts. -/
theorem translatedHilbertGluedChart_jointly_surjective (x : translatedHilbertGlued f hL a) :
    ∃ i, ∃ y : (acyclicHilbertTest f (a i).1).left, translatedHilbertGluedChart f hL a i y = x :=
  (translatedHilbertGlueData f hL a).ι_jointly_surjective x

/-- The glued scheme identifies precisely the constructed pairwise overlaps. -/
@[reassoc]
theorem translatedHilbertGluedChart_overlap (i j : ι) :
    (translatedHilbertChartOverlapLeft f hL (a i) (a j)).left ≫
        translatedHilbertGluedChart f hL a i =
      (translatedHilbertChartOverlapRight f hL (a i) (a j)).left ≫
        translatedHilbertGluedChart f hL a j := by
  have h := (translatedHilbertGlueData f hL a).toGlueData.glue_condition i j
  change (translatedHilbertChartOverlapSwap f hL (a i) (a j)).left ≫
    (translatedHilbertChartOverlapLeft f hL (a j) (a i)).left ≫ _ =
      (translatedHilbertChartOverlapLeft f hL (a i) (a j)).left ≫ _ at h
  rw [← Category.assoc, ← Over.comp_left, translatedHilbertChartOverlapSwap_left] at h
  exact h.symm

/-- The full pair intersection is the scheme-theoretic pullback of the glued charts. -/
theorem translatedHilbertGluedChart_isPullback (i j : ι) :
    IsPullback (translatedHilbertChartOverlapLeft f hL (a i) (a j)).left
      (translatedHilbertChartOverlapRight f hL (a i) (a j)).left
      (translatedHilbertGluedChart f hL a i) (translatedHilbertGluedChart f hL a j) where
  w := translatedHilbertGluedChart_overlap f hL a i j
  isLimit' := by
    have h := (translatedHilbertGlueData f hL a).vPullbackConeIsLimit i j
    change IsLimit (PullbackCone.mk (translatedHilbertChartOverlapLeft f hL (a i) (a j)).left
      ((translatedHilbertChartOverlapSwap f hL (a i) (a j)).left ≫
        (translatedHilbertChartOverlapLeft f hL (a j) (a i)).left) _) at h
    exact ⟨by simpa only [← Over.comp_left, translatedHilbertChartOverlapSwap_left] using h⟩

end FLT.Mazur.HilbertChart
