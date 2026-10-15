/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue power-series base cannot map to a mixed-characteristic valuation ring

A closed-fiber comparison over F does not supply a base map from F[[t]] to A.
Every such map already restricts to a coefficient-field map F to A. Positive
residue characteristic with characteristic-zero fraction field rules this out,
independently of any continuity or chosen image of the smoothing parameter.
-/

@[expose] public section
namespace FLT.Mazur
variable {F A : Type*} [CommRing F] [CommRing A]

/-- Every relation on natural constants in the coefficient ring survives a power-series map. -/
theorem powerSeriesBaseMap_natCast_zero (f : PowerSeries F →+* A) (p : ℕ)
    (hp : (p : F) = 0) : (p : A) = 0 := by
  calc
    (p : A) = f (PowerSeries.C (p : F)) := by simp
    _ = 0 := by rw [hp, map_zero, map_zero]

/-- A nonzero natural constant in the target obstructs every power-series base map. -/
theorem not_nonempty_powerSeriesBaseMap (p : ℕ) (hp : (p : F) = 0)
    (hA : (p : A) ≠ 0) : ¬Nonempty (PowerSeries F →+* A) := by
  rintro ⟨f⟩
  exact hA (powerSeriesBaseMap_natCast_zero f p hp)

/-- In positive coefficient characteristic there is no characteristic-zero target base map. -/
theorem not_nonempty_powerSeriesBaseMap_charZero [CharZero A] (p : ℕ) [CharP F p]
    (hp : p ≠ 0) : ¬Nonempty (PowerSeries F →+* A) :=
  not_nonempty_powerSeriesBaseMap p (CharP.cast_eq_zero F p) (Nat.cast_ne_zero.mpr hp)

variable {K : Type*} [Field K] [CharZero K] (V : ValuationSubring K)

/-- The actual mixed-characteristic valuation base cannot receive its residue power series. -/
theorem not_nonempty_residuePowerSeriesBaseMap (p : ℕ)
    [CharP (IsLocalRing.ResidueField V) p] (hp : p ≠ 0) :
    ¬Nonempty (PowerSeries (IsLocalRing.ResidueField V) →+* V) :=
  not_nonempty_powerSeriesBaseMap_charZero p hp

end FLT.Mazur
