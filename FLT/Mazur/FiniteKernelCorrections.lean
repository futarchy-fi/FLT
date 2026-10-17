/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Corrections in finite coordinates for a ring kernel

A finite ideal frame parametrizes every change of an ambient lift. The
coefficients belong to the ambient ring, so a difference of two ring maps
must be expanded using both endpoints; it is not ambient-linear.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteKernelCorrections
variable {Q T C : Type*} [CommRing Q] [CommRing T] [CommRing C]
  (r : Q →+* T) {n : ℕ} (z : Fin n → Q)
  (hz : Ideal.span (Set.range z) = RingHom.ker r)

include hz in
/-- Finite kernel coordinates describe exactly the lifts of a fixed source value. -/
theorem same_image_iff (a b : Q) :
    r b = r a ↔ ∃ c : Fin n → Q, b = a + ∑ j, c j * z j := by
  have hmem : b - a ∈ Ideal.span (Set.range z) ↔ r b = r a := by
    rw [hz, RingHom.mem_ker, map_sub, sub_eq_zero]
  rw [← hmem, Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩

include hz in
/-- The restriction kills every finite-coordinate kernel correction. -/
theorem sum_restrict (c : Fin n → Q) : r (∑ j, c j * z j) = 0 := by
  have hm : (∑ j, c j * z j) ∈ Ideal.span (Set.range z) :=
    Ideal.mem_span_range_iff_exists_fun.mpr ⟨c, rfl⟩
  exact (show (∑ j, c j * z j) ∈ RingHom.ker r from hz ▸ hm)

/-- Each endpoint acts on both the correction coefficient and the kernel generator. -/
theorem difference_sum (p q : Q →+* C) (c : Fin n → Q) :
    p (∑ j, c j * z j) - q (∑ j, c j * z j) =
      ∑ j, (p (c j) * p (z j) - q (c j) * q (z j)) := by
  simp only [map_sum, map_mul, Finset.sum_sub_distrib]

include hz in
/-- Invariant lifts are exactly solutions to the finite correction equation. -/
theorem invariant_lift_iff (p q : Q →+* C) (a : Q) :
    (∃ b : Q, r b = r a ∧ p b = q b) ↔
      ∃ c : Fin n → Q, p a - q a +
        ∑ j, (p (c j) * p (z j) - q (c j) * q (z j)) = 0 := by
  constructor
  · rintro ⟨b, hb, he⟩
    obtain ⟨c, rfl⟩ := (same_image_iff r z hz a b).mp hb
    refine ⟨c, ?_⟩
    rw [← difference_sum]
    have hh : p (a + ∑ j, c j * z j) - q (a + ∑ j, c j * z j) = 0 :=
      sub_eq_zero.mpr he
    simp only [map_add] at hh
    linear_combination hh
  · rintro ⟨c, hc⟩
    refine ⟨a + ∑ j, c j * z j, ?_, ?_⟩
    · exact (same_image_iff r z hz a _).mpr ⟨c, rfl⟩
    · apply sub_eq_zero.mp
      rw [← difference_sum] at hc
      simp only [map_add]
      linear_combination hc

include hz in
/-- An invariant multiplier scales the defect but keeps the same finite kernel frame. -/
theorem scaled_invariant_lift_iff (p q : Q →+* C) (s a : Q) (hs : p s = q s) :
    (∃ b : Q, r b = r s * r a ∧ p b = q b) ↔
      ∃ c : Fin n → Q, p s * (p a - q a) +
        ∑ j, (p (c j) * p (z j) - q (c j) * q (z j)) = 0 := by
  rw [← map_mul, invariant_lift_iff r z hz p q (s * a)]
  simp only [map_mul, ← hs, mul_sub]

end FLT.Mazur.FiniteKernelCorrections
