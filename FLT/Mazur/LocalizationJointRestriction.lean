/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Jointly faithful restrictions after principal localization

Two ring restrictions that jointly detect equality still do so after inverting
the same denominator. No normalization or nonvanishing hypothesis is needed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizationJointRestriction

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Restrict a fraction by restricting its numerator and denominator. -/
def restriction (f : R →+* S) (s : R) :
    Localization.Away s →+* Localization.Away (f s) :=
  IsLocalization.Away.map _ _ f s

@[simp]
lemma restriction_algebraMap (f : R →+* S) (s a : R) :
    restriction f s (algebraMap R (Localization.Away s) a) =
      algebraMap S (Localization.Away (f s)) (f a) := by
  simp [restriction, IsLocalization.Away.map]

@[simp]
lemma restriction_invSelf (f : R →+* S) (s : R) :
    restriction f s (IsLocalization.Away.invSelf s) =
      IsLocalization.Away.invSelf (f s) := by
  apply (IsLocalization.Away.algebraMap_isUnit (f s)).mul_left_cancel
  rw [IsLocalization.Away.mul_invSelf, ← restriction_algebraMap, ← map_mul,
    IsLocalization.Away.mul_invSelf, map_one]

/-- Polynomial-over-denominator computations commute with restriction. -/
lemma restriction_fraction (f : R →+* S) (s a : R) (n : ℕ) :
    restriction f s (algebraMap R (Localization.Away s) a *
      IsLocalization.Away.invSelf s ^ n) =
      algebraMap S (Localization.Away (f s)) (f a) *
        IsLocalization.Away.invSelf (f s) ^ n := by
  simp

/-- Faithful ring restrictions remain faithful on the matching principal opens. -/
lemma restriction_injective (f : R →+* S) (s : R) (hf : Function.Injective f) :
    Function.Injective (restriction f s) := by
  apply (IsLocalization.Away.map_injective_iff _ _ _).mpr
  intro a ha
  exact ⟨0, by simp [hf (ha.trans (map_zero f).symm)]⟩

/-- Both branches, with a common exponent, detect a localized node function. -/
lemma joint_injective (f : R →+* S) (g : R →+* T) (s : R)
    (hfg : ∀ a : R, f a = 0 → g a = 0 → a = 0) :
    Function.Injective ((restriction f s).prod (restriction g s)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hz₁ : restriction f s z = 0 := congrArg Prod.fst hz
  have hz₂ : restriction g s z = 0 := congrArg Prod.snd hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s z
  have ha₁ : algebraMap S (Localization.Away (f s)) (f a) = 0 := by
    have hh := congrArg (restriction f s) ha
    simpa [hz₁] using hh.symm
  have ha₂ : algebraMap T (Localization.Away (g s)) (g a) = 0 := by
    have hh := congrArg (restriction g s) ha
    simpa [hz₂] using hh.symm
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (f s)
    (ha₁.trans (map_zero _).symm)
  obtain ⟨l, hl⟩ := IsLocalization.Away.exists_of_eq (g s)
    (ha₂.trans (map_zero _).symm)
  have hak : s ^ (k + l) * a = 0 := by
    apply hfg
    · simp only [map_mul, map_pow]
      calc
        _ = f s ^ l * (f s ^ k * f a) := by ring
        _ = 0 := by simp_all
    · simp only [map_mul, map_pow]
      calc
        _ = g s ^ k * (g s ^ l * g a) := by ring
        _ = 0 := by simp_all
  have hza : z * algebraMap R (Localization.Away s) s ^ (n + (k + l)) = 0 := by
    rw [pow_add, ← mul_assoc, ha, ← map_pow, ← map_mul, mul_comm a, hak, map_zero]
  exact ((IsLocalization.Away.algebraMap_isUnit s).pow _).mul_right_cancel
    (by simpa using hza)

end FLT.Mazur.LocalizationJointRestriction
