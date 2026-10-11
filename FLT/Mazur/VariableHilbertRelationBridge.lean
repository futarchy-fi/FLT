/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChartRelation
public import FLT.Mazur.BaseOpenHilbertOrbitFibers

/-!
# Comparing the original restricted relation with the variable chart relation

The common source retains equal original Picard classes in both coordinates.
The actual original relation restricted to this source therefore maps to the
full equal-class relation on the parameter, even for non-open translation bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The original source class is exactly the pullback of the chart's class. -/
theorem variableSourceClass_eq_parameter {T : Over (Spec (.of R))}
    (a : T ⟶ variableSourceIntersection f hL d V c) :
    (relativeFppfSheaf f).obj.map (a ≫ variableSourceInclusion f hL d V c).op
      (smoothHilbertSourceSection f hL) =
    (relativeFppfSheaf f).obj.map (a ≫ variableSourceParameter f hL d V c).op
      (variableChartSection f hL d V c) := by
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    variableSourceIntersection_class]

/-- Equal original classes give a unique restricted original relation arrow. -/
theorem variableRestrictedRelation_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ variableSourceIntersection f hL d V c)
    (h : (relativeFppfSheaf f).obj.map (a ≫ variableSourceInclusion f hL d V c).op
      (smoothHilbertSourceSection f hL) =
    (relativeFppfSheaf f).obj.map (b ≫ variableSourceInclusion f hL d V c).op
      (smoothHilbertSourceSection f hL)) :
    ∃! k : T ⟶ baseOpenRestrictedRelation f hL d V c,
      k ≫ baseOpenRestrictedFst f hL d V c = a ∧
        k ≫ baseOpenRestrictedSnd f hL d V c = b := by
  obtain ⟨r, hr, _⟩ := smoothHilbertRelation_lift f hL
    (a ≫ variableSourceInclusion f hL d V c) (b ≫ variableSourceInclusion f hL d V c) h
  let u : T ⟶ baseOpenRelationFirst f hL d V c := pullback.lift r a hr.1
  have hu : u ≫ baseOpenRelationOther f hL d V c = b ≫ variableSourceInclusion f hL d V c := by
    dsimp only [baseOpenRelationOther, u]
    rw [pullback.lift_fst_assoc, hr.2]
  let k : T ⟶ baseOpenRestrictedRelation f hL d V c := pullback.lift u b hu
  have hk₁ : k ≫ baseOpenRestrictedFst f hL d V c = a := by
    dsimp only [baseOpenRestrictedFst, k, u]
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hk₂ : k ≫ baseOpenRestrictedSnd f hL d V c = b := pullback.lift_snd _ _ _
  exact ⟨k, ⟨hk₁, hk₂⟩, fun l hl ↦
    baseOpenRestricted_hom_ext f hL d V c (hl.1.trans hk₁.symm) (hl.2.trans hk₂.symm)⟩

/-- The restricted original relation maps to the full relation on the parameter scheme. -/
def variableRestrictedToChartRelation :
    baseOpenRestrictedRelation f hL d V c ⟶ variableChartRelation f hL d V c :=
  (variableChartRelation_lift f hL d V c
    (baseOpenRestrictedFst f hL d V c ≫ variableSourceParameter f hL d V c)
    (baseOpenRestrictedSnd f hL d V c ≫ variableSourceParameter f hL d V c) (by
      rw [← variableSourceClass_eq_parameter, ← variableSourceClass_eq_parameter,
        ← baseOpenRestrictedToRelation_fst, ← baseOpenRestrictedToRelation_snd]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        smoothHilbertRelation_class])).choose

/-- The comparison retains the first actual parameter endpoint. -/
@[reassoc]
theorem variableRestrictedToChartRelation_fst :
    variableRestrictedToChartRelation f hL d V c ≫ variableChartRelationFst f hL d V c =
      baseOpenRestrictedFst f hL d V c ≫ variableSourceParameter f hL d V c :=
  (variableChartRelation_lift f hL d V c _ _ (by
    rw [← variableSourceClass_eq_parameter, ← variableSourceClass_eq_parameter,
      ← baseOpenRestrictedToRelation_fst, ← baseOpenRestrictedToRelation_snd]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      smoothHilbertRelation_class])).choose_spec.1.1

/-- The comparison retains the second actual parameter endpoint. -/
@[reassoc]
theorem variableRestrictedToChartRelation_snd :
    variableRestrictedToChartRelation f hL d V c ≫ variableChartRelationSnd f hL d V c =
      baseOpenRestrictedSnd f hL d V c ≫ variableSourceParameter f hL d V c :=
  (variableChartRelation_lift f hL d V c _ _ (by
    rw [← variableSourceClass_eq_parameter, ← variableSourceClass_eq_parameter,
      ← baseOpenRestrictedToRelation_fst, ← baseOpenRestrictedToRelation_snd]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      smoothHilbertRelation_class])).choose_spec.1.2

end FLT.Mazur.HilbertChart
