/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertOverlap

/-!
# Identity and restriction laws for translated Hilbert intersections

The same-base diagonal intersection is the original parameter scheme. The class equality
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
  (V : Over (Spec (.of R))) (i j : BaseMarkedHilbertIndex f V)

/-- A map to the actual overlap is determined by its first parameter map. -/
theorem baseMarkedOverlap_hom_ext {U : Over (Spec (.of R))}
    (a b : U ⟶ baseMarkedChartOverlap f hL V i j)
    (h : a ≫ baseMarkedChartOverlapLeft f hL V i j =
      b ≫ baseMarkedChartOverlapLeft f hL V i j) : a = b :=
  (cancel_mono (baseMarkedChartOverlapLeft f hL V i j)).mp h

/-- The two original Picard classes agree after every restriction of an overlap. -/
theorem baseMarkedOverlap_restrict_class {U : Over (Spec (.of R))}
    (a : U ⟶ baseMarkedChartOverlap f hL V i j) :
    variableHilbertPoint f i.1 hL V i.2 U
        (a ≫ baseMarkedChartOverlapLeft f hL V i j) =
      variableHilbertPoint f j.1 hL V j.2 U
        (a ≫ baseMarkedChartOverlapRight f hL V i j) := by
  rw [variableHilbertPoint_natural, variableHilbertPoint_natural,
    baseMarkedChartOverlap_class]

/-- Both projections from a diagonal overlap coincide, by parameter injectivity. -/
theorem baseMarkedOverlap_diagonal_projections :
    baseMarkedChartOverlapLeft f hL V i i =
      baseMarkedChartOverlapRight f hL V i i :=
  variableHilbertPoint_injective_over f i.1 hL V i.2
    (baseMarkedChartOverlap_base f hL V i i).symm
    (baseMarkedChartOverlap_class f hL V i i)

/-- The identity parameter pair lifts to its actual diagonal intersection. -/
def baseMarkedOverlapDiagonal :
    variableHilbertTest f i.1 V ⟶ baseMarkedChartOverlap f hL V i i :=
  (baseMarkedChartOverlap_lift f hL V i i (𝟙 _) (𝟙 _) rfl rfl).choose

@[reassoc (attr := simp)]
lemma baseMarkedOverlapDiagonal_left :
    baseMarkedOverlapDiagonal f hL V i ≫ baseMarkedChartOverlapLeft f hL V i i =
      𝟙 _ :=
  (baseMarkedChartOverlap_lift f hL V i i (𝟙 _) (𝟙 _) rfl rfl).choose_spec.1.1

/-- The diagonal overlap is canonically isomorphic to the unchanged Hilbert chart. -/
def baseMarkedOverlapDiagonalIso :
    baseMarkedChartOverlap f hL V i i ≅ variableHilbertTest f i.1 V where
  hom := baseMarkedChartOverlapLeft f hL V i i
  inv := baseMarkedOverlapDiagonal f hL V i
  hom_inv_id := by
    apply baseMarkedOverlap_hom_ext f hL V i i
    simp only [Category.assoc, baseMarkedOverlapDiagonal_left,
      Category.comp_id, Category.id_comp]
  inv_hom_id := baseMarkedOverlapDiagonal_left f hL V i

instance baseMarkedOverlapLeft_self_isIso :
    IsIso (baseMarkedChartOverlapLeft f hL V i i) :=
  (baseMarkedOverlapDiagonalIso f hL V i).isIso_hom

/-- Swapping a diagonal intersection acts as the identity on the actual scheme. -/
theorem baseMarkedOverlapSwap_self :
    baseMarkedChartOverlapSwap f hL V i i = 𝟙 _ := by
  apply baseMarkedOverlap_hom_ext f hL V i i
  rw [baseMarkedChartOverlapSwap_left, Category.id_comp,
    baseMarkedOverlap_diagonal_projections]

end FLT.Mazur.HilbertChart
