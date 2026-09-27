/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Comparing reduction modulo a prime and its first power
-/

@[expose] public section

namespace PadicInt

/-- Reduction modulo `p¹` and modulo `p` gives the same natural representative. -/
theorem val_toZModPow_one {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    (x.toZModPow 1).val = (toZMod x).val := by
  rw [val_toZMod_eq_zmodRepr]
  change (x.appr 1 : ZMod (p ^ 1)).val = x.zmodRepr
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (x.appr_lt 1)]
  symm
  apply x.zmodRepr_unique
  · simpa only [pow_one] using x.appr_lt 1
  · simpa only [pow_one, ← maximalIdeal_eq_span_p] using appr_spec 1 x

end PadicInt
