/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Combining markings of coprime exponents

Two injective markings with coprime label exponents have disjoint images.
Their product therefore retains both complete label groups faithfully.
-/

@[expose] public section
namespace FLT.Mazur.CoprimeGroupMarkings
variable {A B G : Type*} [Group A] [Group B] [CommGroup G]
  (f : A →* G) (g : B →* G) {m n : ℕ}
  (hm : ∀ a : A, a ^ m = 1) (hn : ∀ b : B, b ^ n = 1) (h : m.Coprime n)

include hm hn h

/-- A point lying in both marked images is the identity. -/
theorem common_value_eq_one {a : A} {b : B} (he : f a = g b) : f a = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes h
  · exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm, map_one])
  · exact orderOf_dvd_of_pow_eq_one (by rw [he, ← map_pow, hn, map_one])

/-- The product of faithful markings with coprime exponents is faithful. -/
theorem coprod_injective (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (f.coprod g) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨a, b⟩ hab
  have he : f a = g b⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left hab
  have ha : f a = 1 := common_value_eq_one f g hm hn h he
  have hb : g b = 1 := by
    change f a * g b = 1 at hab
    simpa only [ha, one_mul] using hab
  exact Prod.ext (hf (ha.trans (map_one f).symm)) (hg (hb.trans (map_one g).symm))

end FLT.Mazur.CoprimeGroupMarkings
