/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DoubleRootComponentBound
public import Mathlib.Tactic.LinearCombination

/-!
# Bounding a simple class together with quadratic labels

An injective quadratic-root label on the remaining nonzero classes bounds
the whole pointed type by four. No splitting hypothesis is needed.
-/

@[expose] public section

namespace FLT.Mazur

/-- Two roots different from a third root of a genuine quadratic must coincide. -/
theorem quadratic_roots_eq_of_ne {F : Type*} [Field F] {a b c t x y : F}
    (ha : a ≠ 0) (ht : a * t ^ 2 + b * t + c = 0)
    (hx : a * x ^ 2 + b * x + c = 0) (hy : a * y ^ 2 + b * y + c = 0)
    (hxt : x ≠ t) (hyt : y ≠ t) : x = y := by
  have hp (z : F) (hz : a * z ^ 2 + b * z + c = 0) :
      (z - t) * (a * z + a * t + b) = 0 := by linear_combination hz - ht
  have hzx := (mul_eq_zero.mp (hp x hx)).resolve_left (sub_ne_zero.mpr hxt)
  have hzy := (mul_eq_zero.mp (hp y hy)).resolve_left (sub_ne_zero.mpr hyt)
  apply mul_left_cancel₀ ha
  linear_combination hzx - hzy

/-- A nonzero quadratic discriminant makes each root simple in every characteristic. -/
theorem quadratic_root_simple_of_discr {F : Type*} [Field F] {a b c t : F}
    (ht : a * t ^ 2 + b * t + c = 0) (hd : b ^ 2 - 4 * a * c ≠ 0) :
    2 * a * t + b ≠ 0 := by
  intro hz
  apply hd
  calc
    b ^ 2 - 4 * a * c = (2 * a * t + b) ^ 2 := by linear_combination -4 * a * ht
    _ = 0 := by simp [hz]

/-- A simple class and injectively labelled quadratic roots give at most four elements. -/
theorem finite_card_le_four_of_simple_or_quadratic {G F : Type*} [Zero G] [Field F]
    (S : G → Prop) (hs : ∀ c d : G, S c → S d → c = d)
    (a b c : F) (ha : a ≠ 0)
    (f : {g : G // g ≠ 0 ∧ ¬ S g} → F) (hf : Function.Injective f)
    (hr : ∀ g, a * f g ^ 2 + b * f g + c = 0) :
    Finite G ∧ Nat.card G ≤ 4 := by
  classical
  have hS : ∃ s : G, ∀ g, S g → g = s := by
    by_cases he : ∃ s, S s
    · obtain ⟨s, hs'⟩ := he
      exact ⟨s, fun g hg => hs g s hg hs'⟩
    · exact ⟨0, fun g hg => False.elim (he ⟨g, hg⟩)⟩
  have hD : ∃ d e : G, ∀ g : {g : G // g ≠ 0 ∧ ¬ S g}, g.val = d ∨ g.val = e := by
    by_cases ht : Nonempty {g : G // g ≠ 0 ∧ ¬ S g}
    · obtain ⟨t⟩ := ht
      by_cases hu : ∃ u : {g : G // g ≠ 0 ∧ ¬ S g}, f u ≠ f t
      · obtain ⟨u, hu⟩ := hu
        refine ⟨t.val, u.val, fun g => ?_⟩
        by_cases hg : f g = f t
        · exact Or.inl (congrArg Subtype.val (hf hg))
        · exact Or.inr (congrArg Subtype.val
            (hf (quadratic_roots_eq_of_ne ha (hr t) (hr g) (hr u) hg hu)))
      · refine ⟨t.val, t.val, fun g => Or.inl ?_⟩
        exact congrArg Subtype.val (hf (by by_contra h; exact hu ⟨g, h⟩))
    · exact ⟨0, 0, fun g => False.elim (ht ⟨g⟩)⟩
  obtain ⟨s, hs'⟩ := hS
  obtain ⟨d, e, hde⟩ := hD
  let q : Fin 4 → G := ![0, s, d, e]
  have hq : Function.Surjective q := by
    intro g
    by_cases hz : g = 0
    · exact ⟨0, hz.symm⟩
    · by_cases hg : S g
      · exact ⟨1, (hs' g hg).symm⟩
      · rcases hde ⟨g, hz, hg⟩ with he | he
        · exact ⟨2, he.symm⟩
        · exact ⟨3, he.symm⟩
  exact ⟨Finite.of_surjective q hq, by simpa using Nat.card_le_card_of_surjective q hq⟩

end FLT.Mazur
