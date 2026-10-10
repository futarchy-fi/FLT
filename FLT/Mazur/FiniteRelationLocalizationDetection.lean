/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationStages
public import FLT.Mazur.FiniteRelationDetection

/-!
# Detecting equalities on localized finite-relation models

Clear a denominator and use finite detection in the unlocalized model.
Thus equality on the limiting principal open already holds at a finite stage,
without requiring the denominator to be regular or the quotient ideal finite.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- A localized section vanishing in the quotient vanishes at a finite stage. -/
theorem exists_transition_zero (s : Finset I) (x : Stage I r s)
    (hx : toQuotient R I r s x = 0) :
    ∃ (t : Finset I) (hst : s ≤ t), transition R I r hst x = 0 := by
  let d := Ideal.Quotient.mk (FiniteRelationModel.relations I s) r
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj d x
  have he : algebraMap (P ⧸ I) (Quotient I r)
      (FiniteRelationModel.toQuotient R I s a) = 0 := by
    have hh := congrArg (toQuotient R I r s) ha
    rw [map_mul, hx, zero_mul, toQuotient_algebraMap] at hh
    exact hh.symm
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (Ideal.Quotient.mk I r)
    (he.trans (map_zero _).symm)
  have hb : FiniteRelationModel.toQuotient R I s (d ^ m * a) =
      FiniteRelationModel.toQuotient R I s 0 := by
    simpa only [map_mul, map_pow, d, FiniteRelationModel.toQuotient_mk, map_zero,
      mul_zero] using hm
  obtain ⟨t, hst, ht⟩ := FiniteRelationModel.exists_transition_eq R I s (d ^ m * a) 0 hb
  let e := Ideal.Quotient.mk (FiniteRelationModel.relations I t) r
  have hd : FiniteRelationModel.transition R I hst d = e :=
    FiniteRelationModel.transition_mk R I hst r
  have hn : transition R I r hst x * algebraMap _ (Stage I r t) e ^ n =
      algebraMap _ (Stage I r t) (FiniteRelationModel.transition R I hst a) := by
    have hh := congrArg (transition R I r hst) ha
    simpa only [map_mul, map_pow, transition_algebraMap, hd] using hh
  have hz : transition R I r hst x * algebraMap _ (Stage I r t) e ^ (n + m) = 0 := by
    calc
      _ = algebraMap _ (Stage I r t) (FiniteRelationModel.transition R I hst a) *
          algebraMap _ (Stage I r t) e ^ m := by rw [pow_add, ← mul_assoc, hn]
      _ = algebraMap _ (Stage I r t)
          (FiniteRelationModel.transition R I hst (d ^ m * a)) := by
        rw [map_mul, map_pow, hd, map_mul, map_pow, mul_comm]
      _ = 0 := by rw [ht, map_zero, map_zero]
  exact ⟨t, hst, ((IsLocalization.Away.algebraMap_isUnit e).pow (n + m)).mul_right_cancel
    (by simpa only [zero_mul] using hz)⟩

/-- Equality on the limiting principal open is detected at a finite relation stage. -/
theorem exists_transition_eq (s : Finset I) (x y : Stage I r s)
    (h : toQuotient R I r s x = toQuotient R I r s y) :
    ∃ (t : Finset I) (hst : s ≤ t), transition R I r hst x = transition R I r hst y := by
  obtain ⟨t, hst, ht⟩ := exists_transition_zero R I r s (x - y)
    (by rw [map_sub, h, sub_self])
  exact ⟨t, hst, sub_eq_zero.mp (by simpa only [map_sub] using ht)⟩

end FLT.Mazur.FiniteRelationLocalization
