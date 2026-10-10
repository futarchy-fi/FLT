/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationHomDescent

/-!
# Localizing a relation system at a finite-stage element

The second denominator can be any element of the first localization, including
the image of an interchart coordinate. Later stages retain its actual image.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationIterated

universe u v

open FiniteRelationLocalization

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I) (d : FiniteRelationLocalization.Stage I r s)

/-- The transported second denominator at a later relation stage. -/
def denominator (t : Set.Ici s) : FiniteRelationLocalization.Stage I r t.val :=
  FiniteRelationLocalization.transition R I r t.property d

/-- The actual iterated localization at a later relation stage. -/
abbrev Stage (t : Set.Ici s) := Localization.Away (denominator R I r s d t)

/-- The original double open, with the second denominator projected to the quotient. -/
abbrev Quotient := Localization.Away (FiniteRelationLocalization.toQuotient R I r s d)

/-- The new models remain finitely presented over the base. -/
instance stage_finitePresentation [Algebra.FinitePresentation R P] (t : Set.Ici s) :
    Algebra.FinitePresentation R (Stage R I r s d t) := inferInstance

/-- Denominators commute with every relation transition. -/
theorem denominator_transition {t q : Set.Ici s} (h : t ≤ q) :
    FiniteRelationLocalization.transition R I r h (denominator R I r s d t) =
      denominator R I r s d q :=
  AlgHom.congr_fun (FiniteRelationLocalization.transition_comp R I r t.property h) d

/-- Every second denominator recovers the same original element. -/
theorem denominator_toQuotient (t : Set.Ici s) :
    FiniteRelationLocalization.toQuotient R I r t.val (denominator R I r s d t) =
      FiniteRelationLocalization.toQuotient R I r s d :=
  AlgHom.congr_fun (FiniteRelationLocalization.toQuotient_comp R I r t.property) d

/-- The target double localization inverts the transitioned denominator. -/
instance transition_away {t q : Set.Ici s} (h : t ≤ q) :
    IsLocalization.Away (FiniteRelationLocalization.transition R I r h (denominator R I r s d t))
      (Stage R I r s d q) := by
  rw [denominator_transition]
  infer_instance

/-- The original double localization inverts the projected denominator. -/
instance toQuotient_away (t : Set.Ici s) :
    IsLocalization.Away
      (FiniteRelationLocalization.toQuotient R I r t.val (denominator R I r s d t))
      (Quotient R I r s d) := by
  rw [denominator_toQuotient]
  infer_instance

/-- Relation transitions on the actual double opens. -/
def transition {t q : Set.Ici s} (h : t ≤ q) :
    Stage R I r s d t →ₐ[R] Stage R I r s d q :=
  IsLocalization.Away.mapₐ _ _ (FiniteRelationLocalization.transition R I r h)
    (denominator R I r s d t)

/-- Projection from each finite double open to the original double open. -/
def toQuotient (t : Set.Ici s) : Stage R I r s d t →ₐ[R] Quotient R I r s d :=
  IsLocalization.Away.mapₐ _ _ (FiniteRelationLocalization.toQuotient R I r t.val)
    (denominator R I r s d t)

/-- Numerators are transported by the first localized transition. -/
@[simp] theorem transition_algebraMap {t q : Set.Ici s} (h : t ≤ q)
    (x : FiniteRelationLocalization.Stage I r t.val) :
    transition R I r s d h (algebraMap _ (Stage R I r s d t) x) =
      algebraMap _ (Stage R I r s d q) (FiniteRelationLocalization.transition R I r h x) := by
  simp [transition, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- Numerators project by the first localized quotient map. -/
@[simp] theorem toQuotient_algebraMap (t : Set.Ici s)
    (x : FiniteRelationLocalization.Stage I r t.val) :
    toQuotient R I r s d t (algebraMap _ (Stage R I r s d t) x) =
      algebraMap _ (Quotient R I r s d) (FiniteRelationLocalization.toQuotient R I r t.val x) :=
  by simp [toQuotient, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- Double-open transitions are surjective. -/
theorem transition_surjective {t q : Set.Ici s} (h : t ≤ q) :
    Function.Surjective (transition R I r s d h) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective _
    (FiniteRelationLocalization.transition_surjective R I r h)

/-- Every original double-open section lifts to every finite double open. -/
theorem toQuotient_surjective (t : Set.Ici s) :
    Function.Surjective (toQuotient R I r s d t) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective _
    (FiniteRelationLocalization.toQuotient_surjective R I r t.val)

/-- The iterated transition maps compose on their full rings. -/
theorem transition_comp {t q k : Set.Ici s} (h : t ≤ q) (h' : q ≤ k) :
    (transition R I r s d h').comp (transition R I r s d h) =
      transition R I r s d (h.trans h') := by
  apply IsLocalization.algHom_ext (Submonoid.powers (denominator R I r s d t))
  apply DFunLike.ext
  intro x
  change transition R I r s d h' (transition R I r s d h (algebraMap _ _ x)) =
    transition R I r s d (h.trans h') (algebraMap _ _ x)
  rw [transition_algebraMap, transition_algebraMap, transition_algebraMap]
  exact congrArg (algebraMap _ (Stage R I r s d k))
    (AlgHom.congr_fun (FiniteRelationLocalization.transition_comp R I r h h') x)

/-- Quotient projections retain all transition squares. -/
theorem toQuotient_comp {t q : Set.Ici s} (h : t ≤ q) :
    (toQuotient R I r s d q).comp (transition R I r s d h) =
      toQuotient R I r s d t := by
  apply IsLocalization.algHom_ext (Submonoid.powers (denominator R I r s d t))
  apply DFunLike.ext
  intro x
  change toQuotient R I r s d q (transition R I r s d h (algebraMap _ _ x)) =
    toQuotient R I r s d t (algebraMap _ _ x)
  rw [transition_algebraMap, toQuotient_algebraMap, toQuotient_algebraMap]
  exact congrArg (algebraMap _ (Quotient R I r s d))
    (AlgHom.congr_fun (FiniteRelationLocalization.toQuotient_comp R I r h) x)

end FLT.Mazur.FiniteRelationIterated
