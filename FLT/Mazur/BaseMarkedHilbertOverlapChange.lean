/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChartChange

/-!
# Translation-base change on the actual open overlaps

The comparison preserves both original Picard classes and original base maps.
The overlap universal property therefore constructs actual scheme morphisms.
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
  {V W : Over (Spec (.of R))} (b : W ⟶ V) (i j : BaseMarkedHilbertIndex f V)
local notation "iW" => baseMarkedIndexChange f b i
local notation "jW" => baseMarkedIndexChange f b j

/-- The changed pair of charts agrees in the target glued scheme. -/
theorem baseMarkedOverlapChange_exists :
    ∃! k : baseMarkedChartOverlap f hL W iW jW ⟶ baseMarkedChartOverlap f hL V i j,
      k ≫ baseMarkedChartOverlapLeft f hL V i j =
        baseMarkedChartOverlapLeft f hL W iW jW ≫ baseMarkedChartChange f b i.1 ∧
      k ≫ baseMarkedChartOverlapRight f hL V i j =
        baseMarkedChartOverlapRight f hL W iW jW ≫ baseMarkedChartChange f b j.1 := by
  apply baseMarkedChartOverlap_lift
  · rw [Category.assoc, Category.assoc, baseMarkedChartChange_base,
      baseMarkedChartChange_base, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ b) (baseMarkedChartOverlap_base f hL W iW jW)
  · rw [baseMarkedChartChange_class, baseMarkedChartChange_class]
    exact baseMarkedChartOverlap_class f hL W iW jW

/-- The canonical map on actual scheme overlaps under translation-base change. -/
def baseMarkedOverlapChange :
    baseMarkedChartOverlap f hL W iW jW ⟶ baseMarkedChartOverlap f hL V i j :=
  (baseMarkedOverlapChange_exists f hL b i j).choose

@[reassoc]
theorem baseMarkedOverlapChange_left :
    baseMarkedOverlapChange f hL b i j ≫ baseMarkedChartOverlapLeft f hL V i j =
      baseMarkedChartOverlapLeft f hL W iW jW ≫ baseMarkedChartChange f b i.1 :=
  (baseMarkedOverlapChange_exists f hL b i j).choose_spec.1.1

@[reassoc]
theorem baseMarkedOverlapChange_right :
    baseMarkedOverlapChange f hL b i j ≫ baseMarkedChartOverlapRight f hL V i j =
      baseMarkedChartOverlapRight f hL W iW jW ≫ baseMarkedChartChange f b j.1 :=
  (baseMarkedOverlapChange_exists f hL b i j).choose_spec.1.2

/-- The chart comparisons respect the original scheme gluing equations. -/
theorem baseMarkedChartChange_glue {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
    (p q : ι) :
    baseMarkedChartOverlapLeft f hL W (baseMarkedIndexChange f b (a p))
        (baseMarkedIndexChange f b (a q)) ≫
      baseMarkedChartChange f b (a p).1 ≫ baseMarkedGluedArrow f hL V a p =
    baseMarkedChartOverlapRight f hL W (baseMarkedIndexChange f b (a p))
        (baseMarkedIndexChange f b (a q)) ≫
      baseMarkedChartChange f b (a q).1 ≫ baseMarkedGluedArrow f hL V a q := by
  rw [← Category.assoc, ← Category.assoc, ← baseMarkedOverlapChange_left,
    ← baseMarkedOverlapChange_right, Category.assoc, Category.assoc,
    baseMarkedGluedArrow_overlap]

end FLT.Mazur.HilbertChart
