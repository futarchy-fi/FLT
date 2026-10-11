/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertOverlapChange

/-!
# Translation-base change on the actual glued scheme

Compatible chart comparisons descend to a scheme morphism. The resulting
relative map retains the specified morphism between the translation bases.
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
  {V W : Over (Spec (.of R))} (b : W ⟶ V)
  {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
local notation "aW" => fun i ↦ baseMarkedIndexChange f b (a i)

/-- Descent of the scheme chart comparisons along the constructed open cover. -/
def baseMarkedGluedChangeHom : baseMarkedGlued f hL W aW ⟶ baseMarkedGlued f hL V a :=
  Multicoequalizer.desc (baseMarkedGlueData f hL W aW).toGlueData.diagram _
    (fun i ↦ (baseMarkedChartChange f b (a i).1).left ≫ baseMarkedGluedChart f hL V a i)
    (by
      rintro ⟨i, j⟩
      change (baseMarkedChartOverlapLeft f hL W (aW i) (aW j)).left ≫ _ =
        ((baseMarkedChartOverlapSwap f hL W (aW i) (aW j)).left ≫
          (baseMarkedChartOverlapLeft f hL W (aW j) (aW i)).left) ≫ _
      rw [← Over.comp_left, baseMarkedChartOverlapSwap_left]
      exact congrArg Over.Hom.left (baseMarkedChartChange_glue f hL b a i j))

@[reassoc]
theorem baseMarkedGluedChangeHom_chart (i : ι) :
    baseMarkedGluedChart f hL W aW i ≫ baseMarkedGluedChangeHom f hL b a =
      (baseMarkedChartChange f b (a i).1).left ≫ baseMarkedGluedChart f hL V a i :=
  Multicoequalizer.π_desc (baseMarkedGlueData f hL W aW).toGlueData.diagram _ _ _ i

/-- The descended comparison commutes with the original translation-base morphism. -/
@[reassoc]
theorem baseMarkedGluedChangeHom_base :
    baseMarkedGluedChangeHom f hL b a ≫ baseMarkedGluedToTranslationBase f hL V a =
      baseMarkedGluedToTranslationBase f hL W aW ≫ b.left := by
  apply (baseMarkedGluedCover f hL W aW).hom_ext
  intro i
  change baseMarkedGluedChart f hL W aW i ≫ _ =
    baseMarkedGluedChart f hL W aW i ≫ _
  rw [baseMarkedGluedChangeHom_chart_assoc, baseMarkedGluedChart_translationBase,
    baseMarkedGluedChart_translationBase_assoc]
  exact congrArg Over.Hom.left (baseMarkedChartChange_base f b (a i).1)

/-- The actual comparison as a map between original relative tests. -/
def baseMarkedGluedChange : baseMarkedGluedTest f hL W aW ⟶ baseMarkedGluedTest f hL V a :=
  Over.homMk (baseMarkedGluedChangeHom f hL b a) (by
    change _ ≫ baseMarkedGluedToTranslationBase f hL V a ≫ V.hom = _
    rw [← Category.assoc, baseMarkedGluedChangeHom_base, Category.assoc, b.w]
    rfl)

@[reassoc]
theorem baseMarkedGluedChange_base :
    baseMarkedGluedChange f hL b a ≫ baseMarkedGluedBase f hL V a =
      baseMarkedGluedBase f hL W aW ≫ b :=
  Over.OverMorphism.ext (baseMarkedGluedChangeHom_base f hL b a)

@[reassoc]
theorem baseMarkedGluedChange_chart (i : ι) :
    baseMarkedGluedArrow f hL W aW i ≫ baseMarkedGluedChange f hL b a =
      baseMarkedChartChange f b (a i).1 ≫ baseMarkedGluedArrow f hL V a i :=
  Over.OverMorphism.ext (baseMarkedGluedChangeHom_chart f hL b a i)

end FLT.Mazur.HilbertChart
