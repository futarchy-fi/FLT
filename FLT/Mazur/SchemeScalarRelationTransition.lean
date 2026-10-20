/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarRelationPullback

/-!
# Transition maps for full scalar-test equalizers

A morphism of scalar tests induces pullback of the actual source and full
relation, hence restriction of their coefficient equalizers. Ambient lifts
are coherent under these transitions, with no inverse-limit assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarRelationPullback
variable {X D S Y Y' : Scheme} (p q : D ⟶ X) (s : X ⟶ S)
  (hs : p ≫ s = q ≫ s) (b : Y ⟶ S) (b' : Y' ⟶ S)
  (g : Y' ⟶ Y) (hg : g ≫ b = b')

/-- The actual source pullback transition over the unchanged source. -/
def sourceChange : testSource s b' ⟶ testSource s b :=
  pullback.lift (pullback.fst s b') (pullback.snd s b' ≫ g)
    (by rw [Category.assoc, hg, pullback.condition])

@[simp, reassoc]
theorem sourceChange_fst : sourceChange s b b' g hg ≫ pullback.fst s b =
    pullback.fst s b' := pullback.lift_fst _ _ _

@[simp, reassoc]
theorem sourceChange_snd : sourceChange s b b' g hg ≫ pullback.snd s b =
    pullback.snd s b' ≫ g := pullback.lift_snd _ _ _

/-- The transition retains the full original first endpoint. -/
@[reassoc] theorem sourceChange_first :
    sourceChange (p ≫ s) b b' g hg ≫ testFirst p s b =
      testFirst p s b' ≫ sourceChange s b b' g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testFirst_fst, sourceChange_fst, sourceChange_fst_assoc]
  · simp only [Category.assoc, testFirst, pullback.lift_snd,
      sourceChange_snd, pullback.lift_snd_assoc]

/-- The independent second endpoint is retained by the same transition. -/
@[reassoc] theorem sourceChange_second :
    sourceChange (p ≫ s) b b' g hg ≫ testSecond p q s hs b =
      testSecond p q s hs b' ≫ sourceChange s b b' g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testSecond_fst, sourceChange_fst, sourceChange_fst_assoc]
  · simp only [Category.assoc, testSecond, pullback.lift_snd,
      sourceChange_snd, pullback.lift_snd_assoc]

/-- Pulling a compatible coefficient along a scalar transition preserves its full equations. -/
theorem sourceChange_mem (a : testInvariants p q s hs b) :
    (sourceChange s b b' g hg).appTop a.val ∈ testInvariants p q s hs b' := by
  change (testFirst p s b').appTop ((sourceChange s b b' g hg).appTop a.val) =
    (testSecond p q s hs b').appTop ((sourceChange s b b' g hg).appTop a.val)
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    ← sourceChange_first, ← sourceChange_second]
  have ha := a.property
  change (testFirst p s b).appTop a.val = (testSecond p q s hs b).appTop a.val at ha
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
    congrArg (fun x ↦ (sourceChange (p ≫ s) b b' g hg).appTop x) ha

/-- The actual ring homomorphism between full test equalizers. -/
def invariantChange : testInvariants p q s hs b →+* testInvariants p q s hs b' :=
  ((sourceChange s b b' g hg).appTop.hom.comp
    (testInvariants p q s hs b).subtype).codRestrict _ (sourceChange_mem p q s hs b b' g hg)

/-- Every ambient invariant lift is coherent under arbitrary scalar-test transitions. -/
theorem invariantChange_lift (a : Γ(X, ⊤))
    (ha : (pullback.fst (p ≫ s) b ≫ p).appTop a =
      (pullback.fst (p ≫ s) b ≫ q).appTop a)
    (ha' : (pullback.fst (p ≫ s) b' ≫ p).appTop a =
      (pullback.fst (p ≫ s) b' ≫ q).appTop a) :
    invariantChange p q s hs b b' g hg (invariantLift p q s hs b a ha) =
      invariantLift p q s hs b' a ha' := by
  apply Subtype.ext
  change (sourceChange s b b' g hg).appTop ((pullback.fst s b).appTop a) = _
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, sourceChange_fst]
  rfl

end FLT.Mazur.SchemeScalarRelationPullback
