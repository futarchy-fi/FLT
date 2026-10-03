/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Scaled formal exponential and logarithm

Conjugating a formal series by X ↦ aX preserves composition. The scaled
series (exp(aX)-1)/a and log(1+aX)/a are therefore formal inverses.
These algebraic identities will be evaluated in the complete integer ring.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open PowerSeries

variable {L : Type*} [Field L]

/-- Conjugation of a formal series by multiplication by a scalar. -/
def localScaledSeries (a : L) (f : PowerSeries L) : PowerSeries L :=
  a⁻¹ • rescale a f

/-- A scaled series retains zero constant term. -/
theorem localScaledSeries_constantCoeff (a : L) {f : PowerSeries L}
    (hf : constantCoeff f = 0) : constantCoeff (localScaledSeries a f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff] at hf ⊢
  simp [localScaledSeries, hf]

/-- Scaling commutes with formal composition when the inner series has zero constant term. -/
theorem localScaledSeries_subst (a : L) (ha : a ≠ 0) (f g : PowerSeries L)
    (hg : constantCoeff g = 0) :
    (localScaledSeries a f).subst (localScaledSeries a g) =
      localScaledSeries a (f.subst g) := by
  have hgs := HasSubst.of_constantCoeff_zero (localScaledSeries_constantCoeff a hg)
  have hg' := HasSubst.of_constantCoeff_zero hg
  unfold localScaledSeries at hgs ⊢
  rw [subst_smul hgs, rescale_eq_subst a f,
    subst_comp_subst_apply (HasSubst.smul_X' a) hgs, subst_smul hgs, subst_X hgs,
    smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [rescale_eq_subst a (f.subst g), subst_comp_subst_apply hg' (HasSubst.smul_X' a),
    ← rescale_eq_subst]

/-- Scaling fixes the identity series. -/
theorem localScaledSeries_X (a : L) (ha : a ≠ 0) :
    localScaledSeries a (X : PowerSeries L) = X := by
  rw [localScaledSeries, rescale_X, ← smul_eq_C_mul, smul_smul, inv_mul_cancel₀ ha,
    one_smul]

variable [CharZero L]

/-- Scaled exp minus one composed with scaled log is the identity series. -/
theorem localScaledExp_subst_log (a : L) (ha : a ≠ 0) :
    (localScaledSeries a (exp L - 1)).subst (localScaledSeries a (log L)) = X := by
  rw [localScaledSeries_subst a ha _ _ constantCoeff_log,
    subst_sub HasSubst.log, subst_exp_log]
  have h1 : (1 : PowerSeries L).subst (log L) = 1 := by
    rw [← coe_substAlgHom HasSubst.log, map_one]
  rw [h1, add_sub_cancel_left, localScaledSeries_X a ha]

/-- Scaled log composed with scaled exp minus one is the identity series. -/
theorem localScaledLog_subst_exp (a : L) (ha : a ≠ 0) :
    (localScaledSeries a (log L)).subst (localScaledSeries a (exp L - 1)) = X := by
  rw [localScaledSeries_subst a ha _ _ (by simp), subst_log_exp_sub_one,
    localScaledSeries_X a ha]

end LocalClassFieldTheory
