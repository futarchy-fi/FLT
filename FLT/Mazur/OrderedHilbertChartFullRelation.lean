/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertBaseOpenRelation
public import FLT.Mazur.VariableHilbertChartRelationOperations

/-!
# The full restricted relation for arbitrary translation bases

The original relation on the entire constructed source is restricted to a
translated chart without requiring an open translation base. Its endpoints
have equal original classes, although their actual parameters may differ.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hL
local notation "sZ" => variableChartSection f hL d V c

/-- Parameter and original-source class agree after every further test map. -/
theorem full_parameter_class {T : Over (Spec (.of R))}
    (a : T ⟶ source f hL d V c) :
    (relativeFppfSheaf f).obj.map (a ≫ inclusion f hL d V c).op sU =
      (relativeFppfSheaf f).obj.map (a ≫ projection f hL d V c).op sZ := by
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, original_class]

/-- The full restricted endpoints have equal classes, without equal-parameter assumptions. -/
theorem full_restricted_class :
    (relativeFppfSheaf f).obj.map (restrictedFst f hL d V c ≫ inclusion f hL d V c).op sU =
      (relativeFppfSheaf f).obj.map (restrictedSnd f hL d V c ≫ inclusion f hL d V c).op sU := by
  rw [← restrictedToRelation_fst, ← restrictedToRelation_snd]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    OrderedHilbertIdentityOriginalRelation.equal_class]

/-- Every original equal-class pair lifts to the unchanged double scheme restriction. -/
theorem full_restricted_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ source f hL d V c)
    (h : (relativeFppfSheaf f).obj.map (a ≫ inclusion f hL d V c).op sU =
      (relativeFppfSheaf f).obj.map (b ≫ inclusion f hL d V c).op sU) :
    ∃! k : T ⟶ restrictedRelation f hL d V c,
      k ≫ restrictedFst f hL d V c = a ∧ k ≫ restrictedSnd f hL d V c = b := by
  obtain ⟨r, hr, _⟩ := OrderedHilbertIdentityOriginalRelation.lift f hL
    (a ≫ inclusion f hL d V c) (b ≫ inclusion f hL d V c) h
  let u : T ⟶ relationFirst f hL d V c := pullback.lift r a hr.1
  have hu : u ≫ relationOther f hL d V c = b ≫ inclusion f hL d V c := by
    dsimp only [relationOther, u]
    rw [pullback.lift_fst_assoc, hr.2]
  let k : T ⟶ restrictedRelation f hL d V c := pullback.lift u b hu
  have hk₁ : k ≫ restrictedFst f hL d V c = a := by
    dsimp only [restrictedFst, k, u]
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hk₂ : k ≫ restrictedSnd f hL d V c = b := pullback.lift_snd _ _ _
  exact ⟨k, ⟨hk₁, hk₂⟩, fun l hl ↦
    restricted_hom_ext f hL d V c (hl.1.trans hk₁.symm) (hl.2.trans hk₂.symm)⟩

/-- The entire restricted original relation maps to the full parameter relation. -/
def fullRelationToChart :
    restrictedRelation f hL d V c ⟶ variableChartRelation f hL d V c :=
  variableChartRelationLift f hL d V c
    (restrictedFst f hL d V c ≫ projection f hL d V c)
    (restrictedSnd f hL d V c ≫ projection f hL d V c) (by
      rw [← full_parameter_class, ← full_parameter_class]
      exact full_restricted_class f hL d V c)

/-- The first independent parameter is preserved. -/
@[reassoc]
theorem fullRelationToChart_fst :
    fullRelationToChart f hL d V c ≫ variableChartRelationFst f hL d V c =
      restrictedFst f hL d V c ≫ projection f hL d V c :=
  variableChartRelationLift_fst f hL d V c _ _ _

/-- The second independent parameter is preserved. -/
@[reassoc]
theorem fullRelationToChart_snd :
    fullRelationToChart f hL d V c ≫ variableChartRelationSnd f hL d V c =
      restrictedSnd f hL d V c ≫ projection f hL d V c :=
  variableChartRelationLift_snd f hL d V c _ _ _

end FLT.Mazur.OrderedHilbertBaseOpenChart
