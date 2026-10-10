/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPowerSeriesBase

/-!
# Reconstructing coefficients from the original truncated polynomial stages

Adjacent compatibility suffices to recover a unique power series. The proof
uses the actual stage maps and parameter-adic completeness of the coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type*) [CommRing R]

/-- Equality at an actual stage is congruence modulo the corresponding parameter power. -/
theorem seriesToStage_eq_iff (m : ℕ) (f g : PowerSeries R) :
    seriesToStage R m f = seriesToStage R m g ↔
      f - g ∈ parameterIdeal R ^ (m + 1) := by
  rw [← seriesToStage_ker, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, map_sub, sub_eq_zero]

/-- Equality at a higher order implies equality at every smaller order. -/
theorem seriesToStage_eq_of_le {a b : ℕ} (hab : a ≤ b) {f g : PowerSeries R}
    (he : seriesToStage R b f = seriesToStage R b g) :
    seriesToStage R a f = seriesToStage R a g :=
  (seriesToStage_eq_iff R a f g).mpr
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1)
      ((seriesToStage_eq_iff R b f g).mp he))

/-- Every actual truncation together detects a power series uniquely. -/
theorem seriesToStage_ext {f g : PowerSeries R}
    (he : ∀ m, seriesToStage R m f = seriesToStage R m g) : f = g := by
  apply sub_eq_zero.mp
  apply IsHausdorff.haus' (I := parameterIdeal R)
  intro m
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ m)
    ((seriesToStage_eq_iff R m f g).mp (he m))

/-- Lifts of an adjacent-compatible coefficient tower agree at every lower order. -/
theorem stageLifts_compatible (s : ∀ m, Ring R m)
    (hs : ∀ m, restriction R m (s (m + 1)) = s m)
    (u : ℕ → PowerSeries R) (hu : ∀ m, seriesToStage R m (u m) = s m)
    {a b : ℕ} (hab : a ≤ b) : seriesToStage R a (u b) = s a := by
  induction hab with
  | refl => exact hu a
  | @step b hab ih =>
    have hb : seriesToStage R b (u (b + 1)) = seriesToStage R b (u b) := by
      rw [hu b, ← hs b, ← hu (b + 1)]
      exact congrArg (fun f : PowerSeries R →ₐ[R] Ring R b ↦ f (u (b + 1)))
        (restriction_seriesToStage R b).symm
    exact (seriesToStage_eq_of_le R hab hb).trans ih

/-- Every compatible tower of actual truncated coefficients comes from a power series. -/
theorem exists_seriesOfStages (s : ∀ m, Ring R m)
    (hs : ∀ m, restriction R m (s (m + 1)) = s m) :
    ∃ f : PowerSeries R, ∀ m, seriesToStage R m f = s m := by
  choose u hu using fun m ↦ seriesToStage_surjective R m (s m)
  have hc : ∀ {a b : ℕ}, a ≤ b →
      u a ≡ u b [SMOD (parameterIdeal R ^ a • ⊤ : Ideal (PowerSeries R))] := by
    intro a b hab
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    apply Ideal.pow_le_pow_right (Nat.le_succ a)
    apply (seriesToStage_eq_iff R a _ _).mp
    rw [hu a, stageLifts_compatible R s hs u hu hab]
  obtain ⟨f, hf⟩ := IsPrecomplete.prec
    (inferInstance : IsPrecomplete (parameterIdeal R) (PowerSeries R)) hc
  refine ⟨f, fun m ↦ ?_⟩
  have hm := hf (m + 1)
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at hm
  exact ((seriesToStage_eq_iff R m _ _).mpr hm).symm.trans
    (stageLifts_compatible R s hs u hu (Nat.le_succ m))

/-- The uniquely reconstructed complete coefficient. -/
def seriesOfStages (s : ∀ m, Ring R m)
    (hs : ∀ m, restriction R m (s (m + 1)) = s m) : PowerSeries R :=
  (exists_seriesOfStages R s hs).choose

/-- Reconstruction retains every original truncated coefficient map. -/
@[simp] theorem seriesToStage_seriesOfStages (s : ∀ m, Ring R m)
    (hs : ∀ m, restriction R m (s (m + 1)) = s m) (m : ℕ) :
    seriesToStage R m (seriesOfStages R s hs) = s m :=
  (exists_seriesOfStages R s hs).choose_spec m

end FLT.Mazur.PolygonInfinitesimalStages
