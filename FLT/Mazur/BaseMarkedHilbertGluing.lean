/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertSchemeCocycle
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Gluing the base-marked Hilbert parameter schemes

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
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)

/-- Forgetting the base preserves the proved pullback cocycle and all open projections. -/
def baseMarkedGlueData : Scheme.GlueData where
  J := ι
  U i := (variableHilbertTest f (a i).1 V).left
  V p := (baseMarkedChartOverlap f hL V (a p.1) (a p.2)).left
  f i j := (baseMarkedChartOverlapLeft f hL V (a i) (a j)).left
  f_id i := by
    change IsIso ((Over.forget _).map (baseMarkedChartOverlapLeft f hL V (a i) (a i)))
    infer_instance
  t i j := (baseMarkedChartOverlapSwap f hL V (a i) (a j)).left
  t_id i := congrArg Over.Hom.left (baseMarkedOverlapSwap_self f hL V (a i))
  t' i j k := baseMarkedSchemeRotate f hL V (a i) (a j) (a k)
  t_fac i j k := baseMarkedSchemeRotate_snd f hL V (a i) (a j) (a k)
  cocycle i j k := baseMarkedSchemeRotate_cocycle f hL V (a i) (a j) (a k)
  f_open i j := baseMarkedChartOverlapLeft_isOpenImmersion f hL V (a i) (a j)

/-- The scheme glued from the actual base-marked Hilbert parameter charts. -/
def baseMarkedGlued : Scheme := (baseMarkedGlueData f hL V a).glued

/-- Inclusion of each original parameter scheme in the constructed glued scheme. -/
def baseMarkedGluedChart (i : ι) :
    (variableHilbertTest f (a i).1 V).left ⟶ baseMarkedGlued f hL V a :=
  (baseMarkedGlueData f hL V a).ι i

instance baseMarkedGluedChart_isOpenImmersion (i : ι) :
    IsOpenImmersion (baseMarkedGluedChart f hL V a i) :=
  (baseMarkedGlueData f hL V a).ι_isOpenImmersion i

/-- The translated charts form an actual open cover of their glued scheme. -/
def baseMarkedGluedCover : (baseMarkedGlued f hL V a).OpenCover :=
  (baseMarkedGlueData f hL V a).openCover

/-- Every point of the glued scheme lies in one of the unchanged parameter charts. -/
theorem baseMarkedGluedChart_jointly_surjective (x : baseMarkedGlued f hL V a) :
    ∃ i, ∃ y : (variableHilbertTest f (a i).1 V).left, baseMarkedGluedChart f hL V a i y = x :=
  (baseMarkedGlueData f hL V a).ι_jointly_surjective x

/-- The glued scheme identifies precisely the constructed pairwise overlaps. -/
@[reassoc]
theorem baseMarkedGluedChart_overlap (i j : ι) :
    (baseMarkedChartOverlapLeft f hL V (a i) (a j)).left ≫
        baseMarkedGluedChart f hL V a i =
      (baseMarkedChartOverlapRight f hL V (a i) (a j)).left ≫
        baseMarkedGluedChart f hL V a j := by
  have h := (baseMarkedGlueData f hL V a).toGlueData.glue_condition i j
  change (baseMarkedChartOverlapSwap f hL V (a i) (a j)).left ≫
    (baseMarkedChartOverlapLeft f hL V (a j) (a i)).left ≫ _ =
      (baseMarkedChartOverlapLeft f hL V (a i) (a j)).left ≫ _ at h
  rw [← Category.assoc, ← Over.comp_left, baseMarkedChartOverlapSwap_left] at h
  exact h.symm

/-- The full pair intersection is the scheme-theoretic pullback of the glued charts. -/
theorem baseMarkedGluedChart_isPullback (i j : ι) :
    IsPullback (baseMarkedChartOverlapLeft f hL V (a i) (a j)).left
      (baseMarkedChartOverlapRight f hL V (a i) (a j)).left
      (baseMarkedGluedChart f hL V a i) (baseMarkedGluedChart f hL V a j) where
  w := baseMarkedGluedChart_overlap f hL V a i j
  isLimit' := by
    have h := (baseMarkedGlueData f hL V a).vPullbackConeIsLimit i j
    change IsLimit (PullbackCone.mk (baseMarkedChartOverlapLeft f hL V (a i) (a j)).left
      ((baseMarkedChartOverlapSwap f hL V (a i) (a j)).left ≫
        (baseMarkedChartOverlapLeft f hL V (a j) (a i)).left) _) at h
    exact ⟨by simpa only [← Over.comp_left, baseMarkedChartOverlapSwap_left] using h⟩

end FLT.Mazur.HilbertChart
