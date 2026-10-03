/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The numerical obstruction for Raynaud coordinate scalings

Raynaud §3.3(a) uses a largest positive scaling valuation and the parameter
relation to force `p - 1 ≤ e`. These are numerical consequences of that
relation; no coordinate presentation or generic morphism is constructed here.
-/

@[expose] public section

namespace RaynaudParameters

variable {ι : Type*} [Finite ι] {p e : ℕ} (next : ι → ι)
  (a b w : ι → ℤ)

/-- A positive scaling valuation in the cyclic parameter relation forces
the ramification bound of Raynaud §3.3(a). -/
theorem scaling_ramification_bound (hp : 1 ≤ p)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ e)
    (hrel : ∀ i, b i + w (next i) = p * w i + a i)
    (hpos : ∃ i, 0 < w i) : p - 1 ≤ e := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ w ⟨i, Finset.mem_univ i⟩
  have hji := hj i (Finset.mem_univ i)
  have hjnext := hj (next j) (Finset.mem_univ _)
  have haj := ha j
  have hbj := hb j
  have hrj := hrel j
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hprod : 0 ≤ ((p : ℤ) - 1) * (w j - 1) := mul_nonneg (by omega) (by omega)
  have hbound : (p : ℤ) ≤ (e : ℤ) + 1 := by nlinarith
  omega

/-- Below the ramification bound all nonnegative scaling valuations vanish. -/
theorem scaling_eq_zero_of_small_ramification (hp : 1 ≤ p) (he : e < p - 1)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ e) (hw : ∀ i, 0 ≤ w i)
    (hrel : ∀ i, b i + w (next i) = p * w i + a i) : ∀ i, w i = 0 := by
  intro i
  by_contra hi
  have hpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
  exact (Nat.not_le_of_gt he)
    (scaling_ramification_bound next a b w hp ha hb hrel ⟨i, hpos⟩)

/-- In particular, ramification index one and `p ≥ 17` force zero scalings. -/
theorem scaling_eq_zero_of_unramified (hp : 17 ≤ p)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1) (hw : ∀ i, 0 ≤ w i)
    (hrel : ∀ i, b i + w (next i) = p * w i + a i) : ∀ i, w i = 0 :=
  scaling_eq_zero_of_small_ramification next a b w (by omega) (e := 1) (by omega)
    ha hb hw hrel

end RaynaudParameters
