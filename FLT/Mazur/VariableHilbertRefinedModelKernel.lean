/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRefinedRelation

/-!
# Refining an actual full Hilbert kernel pair

Composing an original model projection with the actual parameter change
retains exactly the full changed relation. This direction requires no cover
hypothesis and keeps both independent translation coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.VariableHilbertFppfRefinement
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {Z : Over (Spec (.of R))} (π : variableHilbertTest f d V ⟶ Z)
  (H : IsPullback (variableChartRelationFst f hL d V c)
    (variableChartRelationSnd f hL d V c) π π)
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "g" => baseMarkedChartChange f b d
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "P₁" => variableChartRelationFst f hL d W cW
local notation "Q₁" => variableChartRelationSnd f hL d W cW

include H

/-- Equal original model maps are exactly equal original Picard classes. -/
theorem modelProjection_eq_iff {T : Over (Spec (.of R))}
    (a a' : T ⟶ variableHilbertTest f d V) :
    a ≫ π = a' ≫ π ↔
      (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) =
        (relativeFppfSheaf f).obj.map a'.op (variableChartSection f hL d V c) := by
  constructor
  · intro h
    have hc := congrArg ((relativeFppfSheaf f).obj.map (H.lift a a' h).op)
      (variableChartRelation_class f hL d V c)
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      H.lift_fst, H.lift_snd] using hc
  · intro h
    let r := variableChartRelationLift f hL d V c a a' h
    have hr : r ≫ P = a := variableChartRelationLift_fst f hL d V c _ _ _
    have hr' : r ≫ Q = a' := variableChartRelationLift_snd f hL d V c _ _ _
    rw [← hr, ← hr', Category.assoc, Category.assoc, H.w]

/-- The entire refined relation, not a base-diagonal subrelation, is coequalized. -/
theorem refinedModelProjection_condition : P₁ ≫ (g ≫ π) = Q₁ ≫ (g ≫ π) := by
  rw [← Category.assoc, ← Category.assoc]
  apply (modelProjection_eq_iff f hL d c π H _ _).mpr
  rw [class_map, class_map]
  exact variableChartRelation_class f hL d W cW

/-- The actual composite has the full refined relation as its scheme kernel pair. -/
theorem refinedModelProjection_isPullback : IsPullback P₁ Q₁ (g ≫ π) (g ≫ π) := by
  have hc (z : PullbackCone (g ≫ π) (g ≫ π)) :
      (relativeFppfSheaf f).obj.map z.fst.op (variableChartSection f hL d W cW) =
        (relativeFppfSheaf f).obj.map z.snd.op (variableChartSection f hL d W cW) := by
    rw [← class_map, ← class_map]
    apply (modelProjection_eq_iff f hL d c π H _ _).mp
    simpa only [Category.assoc] using z.condition
  let lift (z : PullbackCone (g ≫ π) (g ≫ π)) :=
    variableChartRelation_lift f hL d W cW z.fst z.snd (hc z)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (refinedModelProjection_condition f hL d b c π H) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z k h₁ h₂ ↦ (lift z).choose_spec.2 k ⟨h₁, h₂⟩))

end FLT.Mazur.VariableHilbertFppfRefinement
