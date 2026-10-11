/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSourceIntersection
public import FLT.Mazur.SmoothHilbertRelationOperations

/-!
# The actual equal-class relation on a variable Hilbert chart

The self-intersection represents equality of the original Picard sections,
including pairs with distinct maps to the translation base. It is the full
presheaf kernel pair; it is not the diagonal of the parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The actual equal-class self-intersection of the variable chart. -/
def variableChartRelation : Over (Spec (.of R)) :=
  variableHilbertOverlap f d V c (variableHilbertTest f d V) (variableChartSection f hL d V c)

/-- The first parameter endpoint. -/
def variableChartRelationFst : variableChartRelation f hL d V c ⟶ variableHilbertTest f d V :=
  variableHilbertOverlapToChart f d hL V c _ (variableChartSection f hL d V c)

/-- The second parameter endpoint. -/
def variableChartRelationSnd : variableChartRelation f hL d V c ⟶ variableHilbertTest f d V :=
  variableHilbertOverlapToTest f d V c _ (variableChartSection f hL d V c)

/-- The variable chart map is the Yoneda map of its actual universal section. -/
theorem variableHilbertPicardMap_eq_section :
    variableHilbertPicardMap f d hL V c =
      uliftYonedaEquiv.symm (variableChartSection f hL d V c) := by
  ext T a
  exact (variableChartSection_map f hL d V c a.down).symm

/-- The self-intersection is the full original presheaf kernel pair. -/
theorem variableChartRelation_isPullback :
    IsPullback (uliftYoneda.{1}.map (variableChartRelationFst f hL d V c))
      (uliftYoneda.{1}.map (variableChartRelationSnd f hL d V c))
      (variableHilbertPicardMap f d hL V c) (variableHilbertPicardMap f d hL V c) := by
  have H := variableHilbertPicardMap_isPullback f d hL V c
    (variableHilbertTest f d V) (variableChartSection f hL d V c)
  rwa [← variableHilbertPicardMap_eq_section] at H

/-- Both endpoints retain exactly the same original Picard section. -/
theorem variableChartRelation_class :
    (relativeFppfSheaf f).obj.map (variableChartRelationFst f hL d V c).op
      (variableChartSection f hL d V c) =
    (relativeFppfSheaf f).obj.map (variableChartRelationSnd f hL d V c).op
      (variableChartSection f hL d V c) := by
  rw [variableChartSection_map]
  exact variableHilbertOverlap_class f d hL V c _ _

/-- The actual parameter endpoints determine every relation morphism. -/
theorem variableChartRelation_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ variableChartRelation f hL d V c}
    (h₁ : a ≫ variableChartRelationFst f hL d V c = b ≫ variableChartRelationFst f hL d V c)
    (h₂ : a ≫ variableChartRelationSnd f hL d V c = b ≫ variableChartRelationSnd f hL d V c) :
    a = b :=
  variableHilbertOverlap_hom_ext f d hL V c _ _ h₂ h₁

/-- Equal original classes yield a unique relation arrow on the actual chart. -/
theorem variableChartRelation_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ variableHilbertTest f d V)
    (h : (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) =
      (relativeFppfSheaf f).obj.map b.op (variableChartSection f hL d V c)) :
    ∃! q : T ⟶ variableChartRelation f hL d V c,
      q ≫ variableChartRelationFst f hL d V c = a ∧
        q ≫ variableChartRelationSnd f hL d V c = b := by
  obtain ⟨q, hq, _⟩ := variableHilbertOverlap_lift f d hL V c _
    (variableChartSection f hL d V c) b a (by rwa [← variableChartSection_map])
  exact ⟨q, hq.symm, fun r hr ↦ variableChartRelation_hom_ext f hL d V c
    (hr.1.trans hq.2.symm) (hr.2.trans hq.1.symm)⟩

instance variableChartRelationSnd_smooth [Smooth V.hom] :
    Smooth (variableChartRelationSnd f hL d V c).left :=
  variableHilbertOverlapToTest_smooth f d V c _ _

end FLT.Mazur.HilbertChart
