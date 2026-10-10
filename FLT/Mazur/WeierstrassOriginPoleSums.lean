/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginMonomialPoles

/-!
# Finite sums in the original pole filtration

Pole bounds form additive subgroups. A uniquely highest weight in a finite
sum cannot cancel, even when its coefficient is nilpotent.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The zero function has every original pole bound. -/
theorem originPole_zero (n : ℕ) : HasOriginPoleBound W 0 n :=
  ⟨0, by simp⟩

/-- Negation preserves actual regular numerators. -/
theorem originPole_neg (a : Coordinate W 2) (n : ℕ)
    (h : HasOriginPoleBound W a n) : HasOriginPoleBound W (-a) n := by
  obtain ⟨b, hb⟩ := h
  exact ⟨-b, by simp only [map_neg, hb]; ring⟩

/-- Subtraction preserves the bound on the actual origin neighborhood. -/
theorem originPole_sub (a b : Coordinate W 2) (n : ℕ)
    (ha : HasOriginPoleBound W a n) (hb : HasOriginPoleBound W b n) :
    HasOriginPoleBound W (a - b) n := by
  rw [sub_eq_add_neg]
  exact originPole_add W a (-b) n ha (originPole_neg W b n hb)

/-- A finite sum of functions with a common bound has that bound. -/
theorem originPole_sum {ι : Type*} (s : Finset ι) (a : ι → Coordinate W 2) (n : ℕ)
    (h : ∀ i ∈ s, HasOriginPoleBound W (a i) n) :
    HasOriginPoleBound W (∑ i ∈ s, a i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using originPole_zero W n
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact originPole_add W _ _ n (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- A higher monomial cannot be cancelled by an actual function of strictly smaller bound. -/
theorem originPoleMonomial_add_lower (r : R) (i j n : ℕ) (b : Coordinate W 2)
    (hn : n < 2 * i + 3 * j)
    (hb : HasOriginPoleBound W b (2 * i + 3 * j - 1))
    (h : HasOriginPoleBound W (originPoleMonomial W r i j + b) n) : r = 0 := by
  have hs := originPole_sub W _ b (2 * i + 3 * j - 1)
    (originPole_mono W _ (by omega) h) hb
  rw [add_sub_cancel_right] at hs
  exact originPoleMonomial_lower W r i j _ (by omega) hs

end FLT.Mazur.WeierstrassIntegralChart
