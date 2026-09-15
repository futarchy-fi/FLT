/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Interval.Constants
public import FLT.Odlyzko.PoitouLargeY

/-!
# Certified Poitou correction at degree eighteen

We use `y₀ = (13/16)² = 169/256`.  The rational square avoids a separate square-root
enclosure while retaining more than `0.12` of logarithmic margin in the final comparison.
The first `L` term is evaluated with equation (23); the two small scaled terms use six
terms of equation (22), and the remaining tail uses the certified `y/175` bound.
-/

@[expose] public section

namespace Odlyzko.Poitou

/-- The fixed rational parameter used by the degree-eighteen certificate. -/
noncomputable def y0 : ℝ := 169 / 256

theorem sqrt_y0 : Real.sqrt y0 = 13 / 16 := by
  rw [show y0 = (13 / 16 : ℝ) ^ 2 by norm_num [y0], Real.sqrt_sq]
  norm_num

/-- Certified lower and upper bounds for equation (23) at `y₀`. -/
theorem Lclosed_y0_bounds : 0 ≤ Lclosed y0 ∧ Lclosed y0 ≤ 3364 / 10000 := by
  have hlog := _root_.Odlyzko.Interval.Constants.log_mem (233 / 64) 30 (by norm_num)
  have hatan :=
    _root_.Odlyzko.Interval.Constants.arctan_mem (13 / 8) 10 .digits20
  norm_num [_root_.Odlyzko.Interval.RatIvl.sub,
    _root_.Odlyzko.Interval.Constants.logEnclosure,
    _root_.Odlyzko.Interval.Constants.logArgument,
    _root_.Odlyzko.Interval.Constants.logOneMinusEnclosure,
    _root_.Odlyzko.Interval.Constants.logOneMinusSum,
    _root_.Odlyzko.Interval.Constants.logOneMinusError] at hlog
  norm_num [_root_.Odlyzko.Interval.RatIvl.sub,
    _root_.Odlyzko.Interval.Constants.arctanEnclosure,
    _root_.Odlyzko.Interval.Constants.arctanNonnegativeEnclosure,
    _root_.Odlyzko.Interval.Constants.arctanLargeEnclosure,
    _root_.Odlyzko.Interval.Constants.arctanSmallEnclosure,
    _root_.Odlyzko.Interval.Constants.arctanPartial,
    _root_.Odlyzko.Interval.Constants.piHalfEnclosure,
    _root_.Odlyzko.Interval.Constants.scaleNonneg,
    _root_.Odlyzko.Interval.Constants.piEnclosure] at hatan
  rw [Lclosed, sqrt_y0]
  norm_num [y0, div_eq_mul_inv]
  constructor <;> nlinarith [hlog.1, hlog.2, hatan.1, hatan.2]

/-- Certified upper bound for equation (23) at `y₀`. -/
theorem Lclosed_y0_le : Lclosed y0 ≤ 3364 / 10000 := Lclosed_y0_bounds.2

private theorem L_y0_div_nine_le : L (y0 / 9) ≤ 54679 / 1000000 := by
  have h := abs_L_sub_Lpartial_le (y := y0 / 9) (N := 8) (by norm_num [y0])
    (by norm_num [y0])
  have hu := (abs_le.mp h).2
  have hIco : Finset.Ico 1 8 = {1, 2, 3, 4, 5, 6, 7} := by decide
  rw [Lpartial, hIco] at hu
  norm_num [Lterm, c, cDen, y0] at hu ⊢
  exact hu.trans (by norm_num)

private theorem L_y0_div_twenty_five_le : L (y0 / 25) ≤ 20573 / 1000000 := by
  have h := abs_L_sub_Lpartial_le (y := y0 / 25) (N := 8) (by norm_num [y0])
    (by norm_num [y0])
  have hu := (abs_le.mp h).2
  have hIco : Finset.Ico 1 8 = {1, 2, 3, 4, 5, 6, 7} := by decide
  rw [Lpartial, hIco] at hu
  norm_num [Lterm, c, cDen, y0] at hu ⊢
  exact hu.trans (by norm_num)

/-- A narrow rational enclosure sufficient for the downstream proof. -/
def L1Enclosure : _root_.Odlyzko.Interval.RatIvl := ⟨0, 363 / 1000, by norm_num⟩

/-- The mixed large-`y` Poitou correction at `y₀` lies in `[0, 0.363]`. -/
theorem L1_y0_mem : L1large y0 ∈ (L1Enclosure : Set ℝ) := by
  constructor
  · dsimp [L1Enclosure]
    rw [L1large]
    simpa using add_nonneg Lclosed_y0_bounds.1
      (tsum_nonneg (L := SummationFilter.unconditional ℕ) fun m ↦
        L1term_shift_nonneg (y := y0)
        (by norm_num [y0]) (by norm_num [y0]) m)
  · apply (L1large_le_head_add (by norm_num [y0]) (by norm_num [y0])).trans
    norm_num [L1Enclosure, y0]
    have h0 := Lclosed_y0_le
    have h9 := L_y0_div_nine_le
    have h25 := L_y0_div_twenty_five_le
    norm_num [y0] at h0 h9 h25
    nlinarith

end Odlyzko.Poitou
