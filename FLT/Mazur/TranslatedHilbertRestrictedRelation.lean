/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertSourceIntersection
public import FLT.Mazur.SmoothHilbertRelation

/-!
# The original relation restricted to a translated chart

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
  (i : TranslatedHilbertIndex f)

/-- Equality of chart parameters detects exactly equality of the original source classes. -/
theorem translatedSourceParameter_eq_iff {T : Over (Spec (.of R))}
    (a b : T ⟶ translatedSourceIntersection f hL i) :
    a ≫ translatedSourceParameter f hL i = b ≫ translatedSourceParameter f hL i ↔
      (relativeFppfSheaf f).obj.map (a ≫ translatedSourceInclusion f hL i).op
        (smoothHilbertSourceSection f hL) =
      (relativeFppfSheaf f).obj.map (b ≫ translatedSourceInclusion f hL i).op
        (smoothHilbertSourceSection f hL) := by
  have H (k : T ⟶ translatedSourceIntersection f hL i) :
      (relativeFppfSheaf f).obj.map (k ≫ translatedSourceInclusion f hL i).op
        (smoothHilbertSourceSection f hL) =
      translatedHilbertPicardPoint f i.1 hL i.2 T (k ≫ translatedSourceParameter f hL i) := by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      translatedSourceIntersection_class, ← translatedHilbertChartSection_map]
  rw [H a, H b]
  exact (translatedHilbertPicardPoint_injective f i.1 hL i.2 T).eq_iff.symm

/-- The first pullback keeps original relation arrows with first endpoint in the chart. -/
def translatedRelationFirst : Over (Spec (.of R)) :=
  pullback (smoothHilbertRelationFst f hL) (translatedSourceInclusion f hL i)

/-- Its original second endpoint in the complete Hilbert source. -/
def translatedRelationOther : translatedRelationFirst f hL i ⟶ smoothHilbertSource f :=
  pullback.fst _ _ ≫ smoothHilbertRelationSnd f hL

/-- The actual original relation restricted to both source-chart endpoints. -/
def translatedRestrictedRelation : Over (Spec (.of R)) :=
  pullback (translatedRelationOther f hL i) (translatedSourceInclusion f hL i)

/-- The first endpoint of the actual restricted relation. -/
def translatedRestrictedFst :
    translatedRestrictedRelation f hL i ⟶ translatedSourceIntersection f hL i :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The second endpoint of the actual restricted relation. -/
def translatedRestrictedSnd :
    translatedRestrictedRelation f hL i ⟶ translatedSourceIntersection f hL i :=
  pullback.snd _ _

/-- The restricted relation retains its original relation arrow. -/
def translatedRestrictedToRelation :
    translatedRestrictedRelation f hL i ⟶ smoothHilbertRelation f hL :=
  pullback.fst _ _ ≫ pullback.fst _ _

@[reassoc]
theorem translatedRestrictedToRelation_fst :
    translatedRestrictedToRelation f hL i ≫ smoothHilbertRelationFst f hL =
      translatedRestrictedFst f hL i ≫ translatedSourceInclusion f hL i := by
  dsimp only [translatedRestrictedToRelation, translatedRestrictedFst]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

@[reassoc]
theorem translatedRestrictedToRelation_snd :
    translatedRestrictedToRelation f hL i ≫ smoothHilbertRelationSnd f hL =
      translatedRestrictedSnd f hL i ≫ translatedSourceInclusion f hL i := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = pullback.snd _ _ ≫ _
  rw [Category.assoc]
  exact pullback.condition

/-- The actual restricted relation is coequalized by the chart parameter map. -/
theorem translatedRestricted_condition :
    translatedRestrictedFst f hL i ≫ translatedSourceParameter f hL i =
      translatedRestrictedSnd f hL i ≫ translatedSourceParameter f hL i := by
  apply (translatedSourceParameter_eq_iff f hL i _ _).mpr
  rw [← translatedRestrictedToRelation_fst, ← translatedRestrictedToRelation_snd]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    smoothHilbertRelation_class]

/-- Restricted relation maps are determined by their two endpoints. -/
theorem translatedRestricted_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ translatedRestrictedRelation f hL i}
    (h₁ : a ≫ translatedRestrictedFst f hL i = b ≫ translatedRestrictedFst f hL i)
    (h₂ : a ≫ translatedRestrictedSnd f hL i = b ≫ translatedRestrictedSnd f hL i) :
    a = b := by
  have hr : a ≫ translatedRestrictedToRelation f hL i =
      b ≫ translatedRestrictedToRelation f hL i := by
    apply smoothHilbertRelation_hom_ext f hL
    · simp only [Category.assoc, translatedRestrictedToRelation_fst]
      exact congrArg (fun k ↦ k ≫ translatedSourceInclusion f hL i) h₁
    · simp only [Category.assoc, translatedRestrictedToRelation_snd]
      exact congrArg (fun k ↦ k ≫ translatedSourceInclusion f hL i) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hr
    · exact h₁
  · exact h₂

/-- Equal actual parameters yield a unique arrow of the restricted original relation. -/
theorem translatedRestricted_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ translatedSourceIntersection f hL i)
    (h : a ≫ translatedSourceParameter f hL i = b ≫ translatedSourceParameter f hL i) :
    ∃! k : T ⟶ translatedRestrictedRelation f hL i,
      k ≫ translatedRestrictedFst f hL i = a ∧
        k ≫ translatedRestrictedSnd f hL i = b := by
  obtain ⟨r, hr, _⟩ := smoothHilbertRelation_lift f hL
    (a ≫ translatedSourceInclusion f hL i) (b ≫ translatedSourceInclusion f hL i)
      ((translatedSourceParameter_eq_iff f hL i a b).mp h)
  let u : T ⟶ translatedRelationFirst f hL i := pullback.lift r a hr.1
  have hu : u ≫ translatedRelationOther f hL i = b ≫ translatedSourceInclusion f hL i := by
    dsimp only [translatedRelationOther, u]
    rw [pullback.lift_fst_assoc, hr.2]
  let k : T ⟶ translatedRestrictedRelation f hL i := pullback.lift u b hu
  have hk₁ : k ≫ translatedRestrictedFst f hL i = a := by
    dsimp only [translatedRestrictedFst, k, u]
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hk₂ : k ≫ translatedRestrictedSnd f hL i = b := pullback.lift_snd _ _ _
  exact ⟨k, ⟨hk₁, hk₂⟩, fun l hl ↦
    translatedRestricted_hom_ext f hL i (hl.1.trans hk₁.symm) (hl.2.trans hk₂.symm)⟩

/-- The restricted original relation is the actual scheme kernel pair of the chart cover. -/
theorem translatedRestricted_isPullback :
    IsPullback (translatedRestrictedFst f hL i) (translatedRestrictedSnd f hL i)
      (translatedSourceParameter f hL i) (translatedSourceParameter f hL i) := by
  let lift (z : PullbackCone (translatedSourceParameter f hL i)
      (translatedSourceParameter f hL i)) :=
    translatedRestricted_lift f hL i z.fst z.snd z.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (translatedRestricted_condition f hL i) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2) ?_)
  intro z k h₁ h₂
  exact translatedRestricted_hom_ext f hL i
    (h₁.trans (lift z).choose_spec.1.1.symm) (h₂.trans (lift z).choose_spec.1.2.symm)

end FLT.Mazur.HilbertChart
