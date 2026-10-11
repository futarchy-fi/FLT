/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertGluing

/-!
# The glued scheme retains its actual translation base

The proved overlap equations descend the maps to V, not merely to the
coefficient base. Every parameter chart retains both structure morphisms.
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

/-- The glued scheme maps to the original base of its translations. -/
def baseMarkedGluedToTranslationBase : baseMarkedGlued f hL V a ⟶ V.left :=
  Multicoequalizer.desc (baseMarkedGlueData f hL V a).toGlueData.diagram _
    (fun i ↦ (variableHilbertBase f (a i).1 V).left) (by
      rintro ⟨i, j⟩
      change (baseMarkedChartOverlapLeft f hL V (a i) (a j)).left ≫
          (variableHilbertBase f (a i).1 V).left =
        ((baseMarkedChartOverlapSwap f hL V (a i) (a j)).left ≫
          (baseMarkedChartOverlapLeft f hL V (a j) (a i)).left) ≫
            (variableHilbertBase f (a j).1 V).left
      simp only [← Over.comp_left, baseMarkedChartOverlapSwap_left,
        baseMarkedChartOverlap_base])

@[reassoc (attr := simp)]
lemma baseMarkedGluedChart_translationBase (i : ι) :
    baseMarkedGluedChart f hL V a i ≫ baseMarkedGluedToTranslationBase f hL V a =
      (variableHilbertBase f (a i).1 V).left :=
  Multicoequalizer.π_desc (baseMarkedGlueData f hL V a).toGlueData.diagram _ _ _ i

/-- The glued scheme as an original test, retaining the translation-base factorization. -/
def baseMarkedGluedTest : Over (Spec (.of R)) :=
  Over.mk (baseMarkedGluedToTranslationBase f hL V a ≫ V.hom)

/-- The actual relative map from the glued scheme to its translation base. -/
def baseMarkedGluedBase : baseMarkedGluedTest f hL V a ⟶ V :=
  Over.homMk (baseMarkedGluedToTranslationBase f hL V a)

/-- The parameter chart is a map over the original coefficient base. -/
def baseMarkedGluedArrow (i : ι) :
    variableHilbertTest f (a i).1 V ⟶ baseMarkedGluedTest f hL V a :=
  Over.homMk (baseMarkedGluedChart f hL V a i) (by
    change _ ≫ baseMarkedGluedToTranslationBase f hL V a ≫ V.hom = _
    rw [← Category.assoc, baseMarkedGluedChart_translationBase, Over.w])

instance baseMarkedGluedArrow_isOpenImmersion (i : ι) :
    IsOpenImmersion (baseMarkedGluedArrow f hL V a i).left :=
  baseMarkedGluedChart_isOpenImmersion f hL V a i

/-- Each chart retains its prescribed translation-base map as a relative equality. -/
@[reassoc]
theorem baseMarkedGluedArrow_base (i : ι) :
    baseMarkedGluedArrow f hL V a i ≫ baseMarkedGluedBase f hL V a =
      variableHilbertBase f (a i).1 V :=
  Over.OverMorphism.ext (baseMarkedGluedChart_translationBase f hL V a i)

/-- The relative chart inclusions agree on the constructed same-base intersections. -/
@[reassoc]
theorem baseMarkedGluedArrow_overlap (i j : ι) :
    baseMarkedChartOverlapLeft f hL V (a i) (a j) ≫ baseMarkedGluedArrow f hL V a i =
      baseMarkedChartOverlapRight f hL V (a i) (a j) ≫ baseMarkedGluedArrow f hL V a j :=
  Over.OverMorphism.ext (baseMarkedGluedChart_overlap f hL V a i j)

end FLT.Mazur.HilbertChart
