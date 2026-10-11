/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseOpenHilbertBaseChange
public import FLT.Mazur.VariableHilbertSourceIntersection
public import FLT.Mazur.SmoothHilbertRelation

/-!
# The original relation restricted to a base-open translated chart

Two maps into the actual source intersection have equal chart parameters
exactly when their original source maps are joined by the original relation.
The restriction is constructed by two scheme pullbacks, retaining both
original relation coordinates.
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
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- Equality of chart parameters detects exactly equality of the original source classes. -/
theorem baseOpenSourceParameter_eq_iff {T : Over (Spec (.of R))}
    (a b : T ⟶ variableSourceIntersection f hL d V c) :
    a ≫ variableSourceParameter f hL d V c = b ≫ variableSourceParameter f hL d V c ↔
      (relativeFppfSheaf f).obj.map (a ≫ variableSourceInclusion f hL d V c).op
        (smoothHilbertSourceSection f hL) =
      (relativeFppfSheaf f).obj.map (b ≫ variableSourceInclusion f hL d V c).op
        (smoothHilbertSourceSection f hL) := by
  have H (k : T ⟶ variableSourceIntersection f hL d V c) :
      (relativeFppfSheaf f).obj.map (k ≫ variableSourceInclusion f hL d V c).op
        (smoothHilbertSourceSection f hL) =
      variableHilbertPoint f d hL V c T (k ≫ variableSourceParameter f hL d V c) := by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      variableSourceIntersection_class, ← variableChartSection_map]
  rw [H a, H b]
  exact (baseOpenHilbertPoint_injective f hL d V c T).eq_iff.symm

/-- The first pullback keeps original relation arrows with first endpoint in the chart. -/
def baseOpenRelationFirst : Over (Spec (.of R)) :=
  pullback (smoothHilbertRelationFst f hL) (variableSourceInclusion f hL d V c)

/-- Its original second endpoint in the complete Hilbert source. -/
def baseOpenRelationOther : baseOpenRelationFirst f hL d V c ⟶ smoothHilbertSource f :=
  pullback.fst _ _ ≫ smoothHilbertRelationSnd f hL

/-- The actual original relation restricted to both source-chart endpoints. -/
def baseOpenRestrictedRelation : Over (Spec (.of R)) :=
  pullback (baseOpenRelationOther f hL d V c) (variableSourceInclusion f hL d V c)

/-- The first endpoint of the actual restricted relation. -/
def baseOpenRestrictedFst :
    baseOpenRestrictedRelation f hL d V c ⟶ variableSourceIntersection f hL d V c :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The second endpoint of the actual restricted relation. -/
def baseOpenRestrictedSnd :
    baseOpenRestrictedRelation f hL d V c ⟶ variableSourceIntersection f hL d V c :=
  pullback.snd _ _

/-- The restricted relation retains its original relation arrow. -/
def baseOpenRestrictedToRelation :
    baseOpenRestrictedRelation f hL d V c ⟶ smoothHilbertRelation f hL :=
  pullback.fst _ _ ≫ pullback.fst _ _

omit [IsOpenImmersion V.hom] in
@[reassoc]
theorem baseOpenRestrictedToRelation_fst :
    baseOpenRestrictedToRelation f hL d V c ≫ smoothHilbertRelationFst f hL =
      baseOpenRestrictedFst f hL d V c ≫ variableSourceInclusion f hL d V c := by
  dsimp only [baseOpenRestrictedToRelation, baseOpenRestrictedFst]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

omit [IsOpenImmersion V.hom] in
@[reassoc]
theorem baseOpenRestrictedToRelation_snd :
    baseOpenRestrictedToRelation f hL d V c ≫ smoothHilbertRelationSnd f hL =
      baseOpenRestrictedSnd f hL d V c ≫ variableSourceInclusion f hL d V c := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = pullback.snd _ _ ≫ _
  rw [Category.assoc]
  exact pullback.condition

/-- The actual restricted relation is coequalized by the chart parameter map. -/
theorem baseOpenRestricted_condition :
    baseOpenRestrictedFst f hL d V c ≫ variableSourceParameter f hL d V c =
      baseOpenRestrictedSnd f hL d V c ≫ variableSourceParameter f hL d V c := by
  apply (baseOpenSourceParameter_eq_iff f hL d V c _ _).mpr
  rw [← baseOpenRestrictedToRelation_fst, ← baseOpenRestrictedToRelation_snd]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    smoothHilbertRelation_class]

omit [IsOpenImmersion V.hom] in
/-- Restricted relation maps are determined by their two endpoints. -/
theorem baseOpenRestricted_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ baseOpenRestrictedRelation f hL d V c}
    (h₁ : a ≫ baseOpenRestrictedFst f hL d V c = b ≫ baseOpenRestrictedFst f hL d V c)
    (h₂ : a ≫ baseOpenRestrictedSnd f hL d V c = b ≫ baseOpenRestrictedSnd f hL d V c) :
    a = b := by
  have hr : a ≫ baseOpenRestrictedToRelation f hL d V c =
      b ≫ baseOpenRestrictedToRelation f hL d V c := by
    apply smoothHilbertRelation_hom_ext f hL
    · simp only [Category.assoc, baseOpenRestrictedToRelation_fst]
      exact congrArg (fun k ↦ k ≫ variableSourceInclusion f hL d V c) h₁
    · simp only [Category.assoc, baseOpenRestrictedToRelation_snd]
      exact congrArg (fun k ↦ k ≫ variableSourceInclusion f hL d V c) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hr
    · exact h₁
  · exact h₂

/-- Equal actual parameters yield a unique arrow of the restricted original relation. -/
theorem baseOpenRestricted_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ variableSourceIntersection f hL d V c)
    (h : a ≫ variableSourceParameter f hL d V c = b ≫ variableSourceParameter f hL d V c) :
    ∃! k : T ⟶ baseOpenRestrictedRelation f hL d V c,
      k ≫ baseOpenRestrictedFst f hL d V c = a ∧
        k ≫ baseOpenRestrictedSnd f hL d V c = b := by
  obtain ⟨r, hr, _⟩ := smoothHilbertRelation_lift f hL
    (a ≫ variableSourceInclusion f hL d V c) (b ≫ variableSourceInclusion f hL d V c)
      ((baseOpenSourceParameter_eq_iff f hL d V c a b).mp h)
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

/-- The restricted original relation is the actual scheme kernel pair of the chart cover. -/
theorem baseOpenRestricted_isPullback :
    IsPullback (baseOpenRestrictedFst f hL d V c) (baseOpenRestrictedSnd f hL d V c)
      (variableSourceParameter f hL d V c) (variableSourceParameter f hL d V c) := by
  let lift (z : PullbackCone (variableSourceParameter f hL d V c)
      (variableSourceParameter f hL d V c)) :=
    baseOpenRestricted_lift f hL d V c z.fst z.snd z.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseOpenRestricted_condition f hL d V c) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2) ?_)
  intro z k h₁ h₂
  exact baseOpenRestricted_hom_ext f hL d V c
    (h₁.trans (lift z).choose_spec.1.1.symm) (h₂.trans (lift z).choose_spec.1.2.symm)

end FLT.Mazur.HilbertChart
