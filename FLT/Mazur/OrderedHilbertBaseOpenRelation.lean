/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertBaseOpenChart
public import FLT.Mazur.OrderedHilbertIdentityRelationOperations

/-!
# The entire constructed-source relation restricted to an actual scheme chart

Two maps into the actual source intersection have equal chart parameters
exactly when their original source maps are joined by the original relation.
The restriction is constructed by two scheme pullbacks, retaining both
original relation coordinates.
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
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The first pullback keeps original relation arrows with first endpoint in the chart. -/
def relationFirst : Over (Spec (.of R)) :=
  pullback (OrderedHilbertIdentityOriginalRelation.fst f hL)
    (inclusion f hL d V c)

/-- Its original second endpoint in the complete Hilbert source. -/
def relationOther : relationFirst f hL d V c ⟶
    OrderedHilbertIdentityOriginalSection.sourceTest f hL :=
  pullback.fst _ _ ≫ OrderedHilbertIdentityOriginalRelation.snd f hL

/-- The actual original relation restricted to both source-chart endpoints. -/
def restrictedRelation : Over (Spec (.of R)) :=
  pullback (relationOther f hL d V c) (inclusion f hL d V c)

/-- The first endpoint of the actual restricted relation. -/
def restrictedFst :
    restrictedRelation f hL d V c ⟶ source f hL d V c :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The second endpoint of the actual restricted relation. -/
def restrictedSnd :
    restrictedRelation f hL d V c ⟶ source f hL d V c :=
  pullback.snd _ _

/-- The restricted relation retains its original relation arrow. -/
def restrictedToRelation :
    restrictedRelation f hL d V c ⟶ OrderedHilbertIdentityOriginalRelation.relation f hL :=
  pullback.fst _ _ ≫ pullback.fst _ _

omit [IsOpenImmersion V.hom] in
@[reassoc]
theorem restrictedToRelation_fst :
    restrictedToRelation f hL d V c ≫ OrderedHilbertIdentityOriginalRelation.fst f hL =
      restrictedFst f hL d V c ≫ inclusion f hL d V c := by
  dsimp only [restrictedToRelation, restrictedFst]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

omit [IsOpenImmersion V.hom] in
@[reassoc]
theorem restrictedToRelation_snd :
    restrictedToRelation f hL d V c ≫ OrderedHilbertIdentityOriginalRelation.snd f hL =
      restrictedSnd f hL d V c ≫ inclusion f hL d V c := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = pullback.snd _ _ ≫ _
  rw [Category.assoc]
  exact pullback.condition

/-- The actual restricted relation is coequalized by the chart parameter map. -/
theorem restricted_condition :
    restrictedFst f hL d V c ≫ projection f hL d V c =
      restrictedSnd f hL d V c ≫ projection f hL d V c := by
  apply (projection_eq_iff f hL d V c _ _).mpr
  rw [← restrictedToRelation_fst, ← restrictedToRelation_snd]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    OrderedHilbertIdentityOriginalRelation.equal_class]

omit [IsOpenImmersion V.hom] in
/-- Restricted relation maps are determined by their two endpoints. -/
theorem restricted_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ restrictedRelation f hL d V c}
    (h₁ : a ≫ restrictedFst f hL d V c = b ≫ restrictedFst f hL d V c)
    (h₂ : a ≫ restrictedSnd f hL d V c = b ≫ restrictedSnd f hL d V c) :
    a = b := by
  have hr : a ≫ restrictedToRelation f hL d V c =
      b ≫ restrictedToRelation f hL d V c := by
    apply OrderedHilbertIdentityOriginalRelation.hom_ext f hL
    · simp only [Category.assoc, restrictedToRelation_fst]
      exact congrArg (fun k ↦ k ≫ inclusion f hL d V c) h₁
    · simp only [Category.assoc, restrictedToRelation_snd]
      exact congrArg (fun k ↦ k ≫ inclusion f hL d V c) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hr
    · exact h₁
  · exact h₂

/-- Equal actual parameters yield a unique arrow of the restricted original relation. -/
theorem restricted_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ source f hL d V c)
    (h : a ≫ projection f hL d V c = b ≫ projection f hL d V c) :
    ∃! k : T ⟶ restrictedRelation f hL d V c,
      k ≫ restrictedFst f hL d V c = a ∧
        k ≫ restrictedSnd f hL d V c = b := by
  obtain ⟨r, hr, _⟩ := OrderedHilbertIdentityOriginalRelation.lift f hL
    (a ≫ inclusion f hL d V c) (b ≫ inclusion f hL d V c)
      ((projection_eq_iff f hL d V c a b).mp h)
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

/-- The restricted original relation is the actual scheme kernel pair of the chart cover. -/
theorem restricted_isPullback :
    IsPullback (restrictedFst f hL d V c) (restrictedSnd f hL d V c)
      (projection f hL d V c) (projection f hL d V c) := by
  let lift (z : PullbackCone (projection f hL d V c)
      (projection f hL d V c)) :=
    restricted_lift f hL d V c z.fst z.snd z.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (restricted_condition f hL d V c) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2) ?_)
  intro z k h₁ h₂
  exact restricted_hom_ext f hL d V c
    (h₁.trans (lift z).choose_spec.1.1.symm) (h₂.trans (lift z).choose_spec.1.2.symm)

end FLT.Mazur.OrderedHilbertBaseOpenChart
