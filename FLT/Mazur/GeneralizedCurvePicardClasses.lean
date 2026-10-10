/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence
public import FLT.Mazur.SchemePicardPullback

/-!
# Generalized curves equipped with actual Picard classes

Retain the generalized curve while quotienting its line-bundle class by
compatible curve isomorphisms. This is a target for subgroup divisor classes;
it asserts neither a representing scheme nor existence of a universal curve.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve

/-- A generalized curve together with an actual line-bundle isomorphism class. -/
abbrev picardData (S : Scheme) := Σ E : GeneralizedEllipticCurve S, SchemePicard.Pic E.curve.left

/-- Identify data by a full generalized-curve isomorphism and actual Picard pullback. -/
def picardDataSetoid (S : Scheme) : Setoid (picardData S) where
  r a b := ∃ e : a.1 ≅ b.1, b.2 = SchemePicard.pullback e.inv.curve.left a.2
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨Iso.refl a.1, (SchemePicard.pullback_id a.2).symm⟩
    · rintro a b ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [he, ← SchemePicard.pullback_comp]
      change a.2 = SchemePicard.pullback (e.hom.curve.left ≫ e.inv.curve.left) a.2
      have hi := ((forgetCurve ⋙ Over.forget S).mapIso e).hom_inv_id
      change e.hom.curve.left ≫ e.inv.curve.left = 𝟙 _ at hi
      rw [hi, SchemePicard.pullback_id]
    · rintro a b c ⟨e, he⟩ ⟨d, hd⟩
      refine ⟨e ≪≫ d, ?_⟩
      rw [hd, he, ← SchemePicard.pullback_comp]
      rfl

/-- Isomorphism classes of generalized curves with a Picard class on the total space. -/
def curvePicardClasses (S : Scheme) := Quotient (picardDataSetoid S)

/-- The geometric class of a specified line-bundle class. -/
def curvePicardClass {S : Scheme} (E : GeneralizedEllipticCurve S)
    (a : SchemePicard.Pic E.curve.left) : curvePicardClasses S :=
  Quotient.mk _ ⟨E, a⟩

/-- Base change of the curve and actual pullback of its Picard class. -/
def picardDataPullback {S T : Scheme} (g : T ⟶ S) (a : picardData S) : picardData T :=
  ⟨a.1.baseChange g, SchemePicard.pullback (pullback.fst a.1.curve.hom g) a.2⟩

/-- The original Picard comparison square survives arbitrary base change. -/
theorem picardDataPullback_rel {S T : Scheme} (g : T ⟶ S) {a b : picardData S}
    (h : (picardDataSetoid S).r a b) :
    (picardDataSetoid T).r (picardDataPullback g a) (picardDataPullback g b) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(baseChangeFunctor g).mapIso e, ?_⟩
  change SchemePicard.pullback _ b.2 =
    SchemePicard.pullback (baseChangeMap g e.inv).curve.left (SchemePicard.pullback _ a.2)
  rw [he, ← SchemePicard.pullback_comp, ← SchemePicard.pullback_comp,
    baseChangeMap_fst]

/-- Actual scheme base change descends to the geometric Picard classes. -/
def curvePicardClassesPullback {S T : Scheme} (g : T ⟶ S) :
    curvePicardClasses S → curvePicardClasses T :=
  Quotient.map (picardDataPullback g) (fun _ _ h ↦ picardDataPullback_rel g h)

end FLT.Mazur.GeneralizedEllipticCurve
