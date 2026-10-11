/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertGluedInjectivity
public import FLT.Mazur.BaseMarkedHilbertFullIntersection
public import FLT.Mazur.RelativeOpenUnionGluing

/-!
# Full test intersections of the glued translated Hilbert charts

Unite the full chart intersections in the product of the original test and
translation base. The independent base coordinate is retained throughout.
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
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))
local notation "arrows" =>
  (fun i ↦ variableHilbertOverlapArrow f (Prod.fst (a i)) V (Prod.snd (a i)) U s)

/-- The full intersection is an actual open union in the original product. -/
def baseMarkedFullIntersection : Over (Spec (.of R)) := RelativeOpenUnion.test arrows

/-- Its open inclusion retains both independent base maps. -/
def baseMarkedFullInclusion : baseMarkedFullIntersection f V a U s ⟶ prod U V :=
  RelativeOpenUnion.inclusion arrows

instance baseMarkedFullInclusion_isOpenImmersion :
    IsOpenImmersion (baseMarkedFullInclusion f V a U s).left :=
  inferInstanceAs (IsOpenImmersion (RelativeOpenUnion.inclusion arrows).left)

instance baseMarkedFullInclusion_mono : Mono (baseMarkedFullInclusion f V a U s) :=
  Over.mono_of_mono_left _

/-- The unchanged full chart intersection maps into the union. -/
def baseMarkedFullChart (i : ι) : variableHilbertOverlap f (a i).1 V (a i).2 U s ⟶
    baseMarkedFullIntersection f V a U s := RelativeOpenUnion.chart arrows i

@[reassoc]
theorem baseMarkedFullChart_inclusion (i : ι) :
    baseMarkedFullChart f V a U s i ≫ baseMarkedFullInclusion f V a U s =
      variableHilbertOverlapArrow f (a i).1 V (a i).2 U s :=
  RelativeOpenUnion.chart_inclusion arrows i

/-- The original full intersections cover the constructed scheme, without an assumed coverage. -/
def baseMarkedFullCover : (baseMarkedFullIntersection f V a U s).left.OpenCover :=
  RelativeOpenUnion.cover arrows

/-- Full chart maps agree over the original product because both class and base agree. -/
theorem baseMarkedFullChart_compatible (i j : ι) {W : Over (Spec (.of R))}
    (p : W ⟶ variableHilbertOverlap f (a i).1 V (a i).2 U s)
    (q : W ⟶ variableHilbertOverlap f (a j).1 V (a j).2 U s)
    (h : p ≫ arrows i = q ≫ arrows j) :
    p ≫ variableHilbertOverlapToChart f (a i).1 hL V (a i).2 U s ≫
        baseMarkedGluedArrow f hL V a i =
      q ≫ variableHilbertOverlapToChart f (a j).1 hL V (a j).2 U s ≫
        baseMarkedGluedArrow f hL V a j := by
  have ht : p ≫ variableHilbertOverlapToTest f (a i).1 V (a i).2 U s =
      q ≫ variableHilbertOverlapToTest f (a j).1 V (a j).2 U s := by
    simpa only [variableHilbertOverlapToTest, Category.assoc] using
      congrArg (fun k ↦ k ≫ prod.fst) h
  rw [← Category.assoc, ← Category.assoc]
  apply baseMarkedGlued_chart_class_eq
  · simp only [Category.assoc, variableHilbertOverlapToChart_base]
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ prod.snd) h.symm
  · rw [variableHilbertPoint_natural, variableHilbertPoint_natural,
      variableHilbertOverlap_class, variableHilbertOverlap_class]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ht]

/-- The compatible full chart maps construct a map to the actual glued Hilbert scheme. -/
def baseMarkedFullToGlued :
    baseMarkedFullIntersection f V a U s ⟶ baseMarkedGluedTest f hL V a :=
  RelativeOpenUnion.glue arrows
    (fun i ↦ variableHilbertOverlapToChart f (a i).1 hL V (a i).2 U s ≫
      baseMarkedGluedArrow f hL V a i) (baseMarkedFullChart_compatible f hL V a U s)

@[reassoc]
theorem baseMarkedFullChart_toGlued (i : ι) :
    baseMarkedFullChart f V a U s i ≫ baseMarkedFullToGlued f hL V a U s =
      variableHilbertOverlapToChart f (a i).1 hL V (a i).2 U s ≫
        baseMarkedGluedArrow f hL V a i := RelativeOpenUnion.chart_glue arrows _ _ i

end FLT.Mazur.HilbertChart
