/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertGluedPicard

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
  {ι : Type} (a : ι → TranslatedHilbertIndex f)

/-- Restrict the constructed Picard section along an arbitrary relative test map. -/
def translatedHilbertGluedPoint (U : Over (Spec (.of R)))
    (b : U ⟶ translatedHilbertGluedTest f hL a) : (relativeFppfSheaf f).obj.obj (op U) :=
  (relativeFppfSheaf f).obj.map b.op (translatedHilbertGluedPicard f hL a)

/-- The constructed Picard class is natural on all original relative tests. -/
theorem translatedHilbertGluedPoint_natural {U V : Over (Spec (.of R))}
    (b : V ⟶ U) (k : U ⟶ translatedHilbertGluedTest f hL a) :
    translatedHilbertGluedPoint f hL a V (b ≫ k) =
      (relativeFppfSheaf f).obj.map b.op (translatedHilbertGluedPoint f hL a U k) := by
  simp only [translatedHilbertGluedPoint, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- The actual glued map restricts to the unchanged translated Hilbert parameter class. -/
theorem translatedHilbertGluedPoint_chart (i : ι) {U : Over (Spec (.of R))}
    (b : U ⟶ acyclicHilbertTest f (a i).1) :
    translatedHilbertGluedPoint f hL a U (b ≫ translatedHilbertGluedArrow f hL a i) =
      translatedHilbertPicardPoint f (a i).1 hL (a i).2 U b := by
  rw [translatedHilbertGluedPoint_natural]
  change (relativeFppfSheaf f).obj.map b.op
    ((relativeFppfSheaf f).obj.map (translatedHilbertGluedArrow f hL a i).op
      (translatedHilbertGluedPicard f hL a)) = _
  rw [translatedHilbertGluedPicard_chart, translatedHilbertChartSection_map]

/-- The representing candidate's map to the original Picard presheaf. -/
def translatedHilbertGluedPicardMap :
    uliftYoneda.{1}.obj (translatedHilbertGluedTest f hL a) ⟶
      (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm (translatedHilbertGluedPicard f hL a)

/-- Evaluation of the candidate representing map is the actual restricted Picard class. -/
theorem translatedHilbertGluedPicardMap_apply (U : Over (Spec (.of R)))
    (b : U ⟶ translatedHilbertGluedTest f hL a) :
    (translatedHilbertGluedPicardMap f hL a).app (op U) (ULift.up b) =
      translatedHilbertGluedPoint f hL a U b := rfl

/-- Equality of original chart classes already identifies their maps into the glued scheme. -/
theorem translatedHilbertGlued_chart_class_eq (i j : ι) {U : Over (Spec (.of R))}
    (p : U ⟶ acyclicHilbertTest f (a i).1) (q : U ⟶ acyclicHilbertTest f (a j).1)
    (h : translatedHilbertPicardPoint f (a i).1 hL (a i).2 U p =
      translatedHilbertPicardPoint f (a j).1 hL (a j).2 U q) :
    p ≫ translatedHilbertGluedArrow f hL a i = q ≫ translatedHilbertGluedArrow f hL a j := by
  obtain ⟨b, hb, _⟩ := translatedHilbertChartOverlap_lift f hL (a i) (a j) p q h
  rw [← hb.1, ← hb.2, Category.assoc, Category.assoc, translatedHilbertGluedArrow_overlap]

end FLT.Mazur.HilbertChart
