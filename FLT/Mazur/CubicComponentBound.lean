/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Tactic.LinearCombination

/-!
# Finite bounds from residual cubic labels

A nonzero cubic discriminant makes every rational root simple. Injecting
the nonzero elements of a pointed type into cubic roots bounds that type
by four, without requiring the cubic to split over the base field.
-/

@[expose] public section

namespace FLT.Mazur

/-- A rational root of a monic cubic with nonzero discriminant is simple. -/
theorem monicCubic_root_simple_of_discr_ne_zero {F : Type*} [Field F] {b c d t : F}
    (ht : t ^ 3 + b * t ^ 2 + c * t + d = 0)
    (hd : (Cubic.mk 1 b c d).discr ≠ 0) : 3 * t ^ 2 + 2 * b * t + c ≠ 0 := by
  intro hz
  have hc : c = -3 * t ^ 2 - 2 * b * t := by linear_combination hz
  have he : d = 2 * t ^ 3 + b * t ^ 2 := by linear_combination ht - t * hz
  apply hd
  simp only [Cubic.discr]
  rw [hc, he]
  ring

/-- Injective cubic-root labels for nonzero elements bound a pointed type by four. -/
theorem finite_card_le_four_of_cubic_labels {G F : Type*} [Zero G] [Field F]
    (p : Cubic F) (hp : p.toPoly ≠ 0) (f : {c : G // c ≠ 0} → F)
    (hf : Function.Injective f)
    (hr : ∀ c, p.a * f c ^ 3 + p.b * f c ^ 2 + p.c * f c + p.d = 0) :
    Finite G ∧ Nat.card G ≤ 4 := by
  classical
  let g : {c : G // c ≠ 0} → {t : F // t ∈ p.roots.toFinset} :=
    fun c => ⟨f c, Multiset.mem_toFinset.mpr ((p.mem_roots_iff hp _).mpr (hr c))⟩
  have hg : Function.Injective g := fun c d h => hf (congrArg Subtype.val h)
  have : Finite {c : G // c ≠ 0} := Finite.of_injective g hg
  have : Finite G := Finite.of_equiv _ (Equiv.optionSubtypeNe (0 : G))
  have hc : Nat.card {c : G // c ≠ 0} ≤ 3 := by
    have hn := Nat.card_le_card_of_injective g hg
    have hb : Nat.card {t : F // t ∈ p.roots.toFinset} ≤ 3 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using p.card_roots_le
    exact hn.trans hb
  have he : Nat.card G = Nat.card {c : G // c ≠ 0} + 1 := by
    let := Fintype.ofFinite {c : G // c ≠ 0}
    rw [← Nat.card_congr (Equiv.optionSubtypeNe (0 : G))]
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  exact ⟨inferInstance, by omega⟩

end FLT.Mazur
