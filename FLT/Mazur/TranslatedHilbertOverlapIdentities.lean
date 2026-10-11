/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertChartOverlap

/-!
# Identity and restriction laws for translated Hilbert intersections

The diagonal intersection is the original parameter scheme. The class equality
on an overlap persists under arbitrary test maps, giving the input for triples.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i j : TranslatedHilbertIndex f)

/-- A map to the actual overlap is determined by its first parameter map. -/
theorem translatedHilbertOverlap_hom_ext {U : Over (Spec (.of R))}
    (a b : U ⟶ translatedHilbertChartOverlap f hL i j)
    (h : a ≫ translatedHilbertChartOverlapLeft f hL i j =
      b ≫ translatedHilbertChartOverlapLeft f hL i j) : a = b :=
  (cancel_mono (translatedHilbertChartOverlapLeft f hL i j)).mp h

/-- The two original Picard classes agree after every restriction of an overlap. -/
theorem translatedHilbertOverlap_restrict_class {U : Over (Spec (.of R))}
    (a : U ⟶ translatedHilbertChartOverlap f hL i j) :
    translatedHilbertPicardPoint f i.1 hL i.2 U
        (a ≫ translatedHilbertChartOverlapLeft f hL i j) =
      translatedHilbertPicardPoint f j.1 hL j.2 U
        (a ≫ translatedHilbertChartOverlapRight f hL i j) := by
  rw [translatedHilbertPicardPoint_natural, translatedHilbertPicardPoint_natural,
    translatedHilbertChartOverlap_class]

/-- Both projections from a diagonal overlap coincide, by parameter injectivity. -/
theorem translatedHilbertOverlap_diagonal_projections :
    translatedHilbertChartOverlapLeft f hL i i =
      translatedHilbertChartOverlapRight f hL i i :=
  translatedHilbertPicardPoint_injective f i.1 hL i.2 _
    (translatedHilbertChartOverlap_class f hL i i)

/-- The identity parameter pair lifts to its actual diagonal intersection. -/
def translatedHilbertOverlapDiagonal :
    acyclicHilbertTest f i.1 ⟶ translatedHilbertChartOverlap f hL i i :=
  (translatedHilbertChartOverlap_lift f hL i i (𝟙 _) (𝟙 _) rfl).choose

@[reassoc (attr := simp)]
lemma translatedHilbertOverlapDiagonal_left :
    translatedHilbertOverlapDiagonal f hL i ≫ translatedHilbertChartOverlapLeft f hL i i =
      𝟙 _ :=
  (translatedHilbertChartOverlap_lift f hL i i (𝟙 _) (𝟙 _) rfl).choose_spec.1.1

/-- The diagonal overlap is canonically isomorphic to the unchanged Hilbert chart. -/
def translatedHilbertOverlapDiagonalIso :
    translatedHilbertChartOverlap f hL i i ≅ acyclicHilbertTest f i.1 where
  hom := translatedHilbertChartOverlapLeft f hL i i
  inv := translatedHilbertOverlapDiagonal f hL i
  hom_inv_id := by
    apply translatedHilbertOverlap_hom_ext f hL i i
    simp only [Category.assoc, translatedHilbertOverlapDiagonal_left,
      Category.comp_id, Category.id_comp]
  inv_hom_id := translatedHilbertOverlapDiagonal_left f hL i

instance translatedHilbertOverlapLeft_self_isIso :
    IsIso (translatedHilbertChartOverlapLeft f hL i i) :=
  (translatedHilbertOverlapDiagonalIso f hL i).isIso_hom

/-- Swapping a diagonal intersection acts as the identity on the actual scheme. -/
theorem translatedHilbertOverlapSwap_self :
    translatedHilbertChartOverlapSwap f hL i i = 𝟙 _ := by
  apply translatedHilbertOverlap_hom_ext f hL i i
  rw [translatedHilbertChartOverlapSwap_left, Category.id_comp,
    translatedHilbertOverlap_diagonal_projections]

end FLT.Mazur.HilbertChart
