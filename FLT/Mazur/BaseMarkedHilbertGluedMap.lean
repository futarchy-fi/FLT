/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertGluedPicard

/-!
# The original Picard map of the glued translated charts

The glued section gives an actual natural transformation on every original test.
Its restriction to each Hilbert chart is the original translated class.
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

/-- Restrict the constructed Picard section along an arbitrary relative test map. -/
def baseMarkedGluedPoint (U : Over (Spec (.of R)))
    (b : U ⟶ baseMarkedGluedTest f hL V a) : (relativeFppfSheaf f).obj.obj (op U) :=
  (relativeFppfSheaf f).obj.map b.op (baseMarkedGluedPicard f hL V a)

/-- The constructed Picard class is natural on all original relative tests. -/
theorem baseMarkedGluedPoint_natural {U W : Over (Spec (.of R))}
    (b : W ⟶ U) (k : U ⟶ baseMarkedGluedTest f hL V a) :
    baseMarkedGluedPoint f hL V a W (b ≫ k) =
      (relativeFppfSheaf f).obj.map b.op (baseMarkedGluedPoint f hL V a U k) := by
  simp only [baseMarkedGluedPoint, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- The actual glued map restricts to the unchanged translated Hilbert parameter class. -/
theorem baseMarkedGluedPoint_chart (i : ι) {U : Over (Spec (.of R))}
    (b : U ⟶ variableHilbertTest f (a i).1 V) :
    baseMarkedGluedPoint f hL V a U (b ≫ baseMarkedGluedArrow f hL V a i) =
      variableHilbertPoint f (a i).1 hL V (a i).2 U b := by
  rw [baseMarkedGluedPoint_natural]
  change (relativeFppfSheaf f).obj.map b.op
    ((relativeFppfSheaf f).obj.map (baseMarkedGluedArrow f hL V a i).op
      (baseMarkedGluedPicard f hL V a)) = _
  rw [baseMarkedGluedPicard_chart, baseMarkedChartSection_map]

/-- The representing candidate's map to the original Picard presheaf. -/
def baseMarkedGluedPicardMap :
    uliftYoneda.{1}.obj (baseMarkedGluedTest f hL V a) ⟶
      (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm (baseMarkedGluedPicard f hL V a)

/-- Evaluation of the candidate representing map is the actual restricted Picard class. -/
theorem baseMarkedGluedPicardMap_apply (U : Over (Spec (.of R)))
    (b : U ⟶ baseMarkedGluedTest f hL V a) :
    (baseMarkedGluedPicardMap f hL V a).app (op U) (ULift.up b) =
      baseMarkedGluedPoint f hL V a U b := rfl

/-- Equal original chart classes over the same base map agree in the glued scheme. -/
theorem baseMarkedGlued_chart_class_eq (i j : ι) {U : Over (Spec (.of R))}
    (p : U ⟶ variableHilbertTest f (a i).1 V) (q : U ⟶ variableHilbertTest f (a j).1 V)
    (hb : q ≫ variableHilbertBase f (a j).1 V =
      p ≫ variableHilbertBase f (a i).1 V)
    (h : variableHilbertPoint f (a i).1 hL V (a i).2 U p =
      variableHilbertPoint f (a j).1 hL V (a j).2 U q) :
    p ≫ baseMarkedGluedArrow f hL V a i = q ≫ baseMarkedGluedArrow f hL V a j := by
  obtain ⟨b, hb, _⟩ := baseMarkedChartOverlap_lift f hL V (a i) (a j) p q hb h
  rw [← hb.1, ← hb.2, Category.assoc, Category.assoc, baseMarkedGluedArrow_overlap]

end FLT.Mazur.HilbertChart
