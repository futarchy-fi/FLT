/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationSource
public import FLT.Mazur.AffineHilbertNestedRestriction

/-!
# The full original kernel pair on an actual translation-refined source

The constructed source refinement carries the original relation restricted
at BOTH endpoints. The change of translating chart does not select a smaller
subrelation or lose pairs with different translation coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "u" => translationSourceMap f d b k
local notation "l" => translationSourceChart f d b k
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

/-- The relation of the changed chart equals the original relation on the constructed source. -/
def translationSourceNestedIso : relation f hL d W c' l ≅
    relation f hL d V c (u ≫ k) := by
  rw [translationSource_square]
  exact translationRelationIso f hL d b c l

/-- The actual refined relation is the original FULL scheme double restriction. -/
def translationSourceFullRelationIso : (relation f hL d W c' l).left ≅
    SchemeRelationRestriction.doubleDomain (fst f hL d V c k).left
      (snd f hL d V c k).left (u).left :=
  (Over.forget _).mapIso (translationSourceNestedIso f hL d b c k) ≪≫
    nestedSchemeDoubleIso f hL d V c k u

/-- Original class equality is preserved on all tests, including independent base maps. -/
theorem translationSource_equal_class_iff {T : Over (Spec (.of R))}
    (a z : T ⟶ translationSource f d b k) :
    (relativeFppfSheaf f).obj.map (a ≫ u).op (sectionAt f hL d V c k) =
        (relativeFppfSheaf f).obj.map (z ≫ u).op (sectionAt f hL d V c k) ↔
      (relativeFppfSheaf f).obj.map a.op (sectionAt f hL d W c' l) =
        (relativeFppfSheaf f).obj.map z.op (sectionAt f hL d W c' l) := by
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, translationSource_class]

/-- Every equal ORIGINAL class pair has one and only one arrow in the refined relation. -/
theorem translationSource_original_lift {T : Over (Spec (.of R))}
    (a z : T ⟶ translationSource f d b k)
    (h : (relativeFppfSheaf f).obj.map (a ≫ u).op (sectionAt f hL d V c k) =
      (relativeFppfSheaf f).obj.map (z ≫ u).op (sectionAt f hL d V c k)) :
    ∃! r : T ⟶ relation f hL d W c' l,
      r ≫ fst f hL d W c' l = a ∧ r ≫ snd f hL d W c' l = z :=
  lift f hL d W c' l a z ((translationSource_equal_class_iff f hL d b c k a z).mp h)

end FLT.Mazur.HilbertChart.AffineRestriction
