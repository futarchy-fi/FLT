/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Integer-valued homomorphisms determined by a uniformizer

Kernel containment reduces an order comparison to the image of one
element of order one. The conclusion is derived by dividing out its power.
-/

@[expose] public section

namespace LocalClassFieldTheory

/-- Kernel containment and the image of an order-one element determine the scaling factor. -/
theorem orderHom_scale {G : Type*} [Group G] (o f : G →* Multiplicative ℤ)
    (t : G) (ht : o t = Multiplicative.ofAdd 1) (e : ℕ)
    (he : f t = Multiplicative.ofAdd (e : ℤ))
    (hker : ∀ x, o x = 1 → f x = 1) (x : G) : f x = o x ^ e := by
  let n := (o x).toAdd
  have ho : o (x / t ^ n) = 1 := by
    apply Multiplicative.toAdd.injective
    simp [map_div, map_zpow, ht, n]
  have hf := hker (x / t ^ n) ho
  rw [map_div, map_zpow, div_eq_one] at hf
  rw [hf, he]
  apply Multiplicative.toAdd.injective
  change n • (e : ℤ) = e • (o x).toAdd
  simp [n, mul_comm]

end LocalClassFieldTheory
