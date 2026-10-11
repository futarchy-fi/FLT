/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertGluing

/-!
# The original base of the glued translated charts

All overlap maps preserve the coefficient base, so the actual glued scheme
inherits its base morphism and its unchanged parameter charts are relative maps.
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

/-- The scheme obtained by gluing retains its original coefficient-base structure. -/
def translatedHilbertGluedBase : translatedHilbertGlued f hL a ⟶ Spec (.of R) :=
  Multicoequalizer.desc (translatedHilbertGlueData f hL a).toGlueData.diagram _
    (fun i ↦ (acyclicHilbertTest f (a i).1).hom) (by
      rintro ⟨i, j⟩
      change (translatedHilbertChartOverlapLeft f hL (a i) (a j)).left ≫
          (acyclicHilbertTest f (a i).1).hom =
        ((translatedHilbertChartOverlapSwap f hL (a i) (a j)).left ≫
          (translatedHilbertChartOverlapLeft f hL (a j) (a i)).left) ≫
            (acyclicHilbertTest f (a j).1).hom
      simp only [Category.assoc, Over.w])

@[reassoc (attr := simp)]
lemma translatedHilbertGluedChart_over (i : ι) :
    translatedHilbertGluedChart f hL a i ≫ translatedHilbertGluedBase f hL a =
      (acyclicHilbertTest f (a i).1).hom :=
  Multicoequalizer.π_desc (translatedHilbertGlueData f hL a).toGlueData.diagram _ _ _ i

/-- The actual glued scheme as a test over the original base. -/
def translatedHilbertGluedTest : Over (Spec (.of R)) :=
  Over.mk (translatedHilbertGluedBase f hL a)

/-- Every unchanged parameter chart is an original relative test map. -/
def translatedHilbertGluedArrow (i : ι) :
    acyclicHilbertTest f (a i).1 ⟶ translatedHilbertGluedTest f hL a :=
  Over.homMk (translatedHilbertGluedChart f hL a i)
    (translatedHilbertGluedChart_over f hL a i)

instance translatedHilbertGluedArrow_isOpenImmersion (i : ι) :
    IsOpenImmersion (translatedHilbertGluedArrow f hL a i).left :=
  translatedHilbertGluedChart_isOpenImmersion f hL a i

/-- The relative chart maps agree on precisely the constructed pairwise intersections. -/
@[reassoc]
theorem translatedHilbertGluedArrow_overlap (i j : ι) :
    translatedHilbertChartOverlapLeft f hL (a i) (a j) ≫
        translatedHilbertGluedArrow f hL a i =
      translatedHilbertChartOverlapRight f hL (a i) (a j) ≫
        translatedHilbertGluedArrow f hL a j := by
  apply Over.OverMorphism.ext
  exact translatedHilbertGluedChart_overlap f hL a i j

end FLT.Mazur.HilbertChart
