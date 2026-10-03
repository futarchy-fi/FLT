/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicCarry
public import FLT.LocalClassFieldTheory.TwoExtensionNegativeEvaluation

/-!
# The positive cyclic carry at negative Tate degrees

Summing the carry in its first argument gives the second argument's chosen
integer representative. This makes the inverse convention in the constructed
negative Tate cup explicit.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (n : ℕ) [NeZero n]

/-- Summing the positive carry over the cyclic group gives the integer representative. -/
theorem cyclicCarry_sum (j : ZMod n) :
    (∑ i : ZMod n, cyclicCarry i j) = (j.val : ℤ) := by
  apply mul_right_cancel₀ (show (n : ℤ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne n))
  rw [Finset.sum_mul]
  simp only [cyclicCarry_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have h : (∑ i : ZMod n, ((i + j).val : ℤ)) = ∑ i : ZMod n, (i.val : ℤ) :=
    Equiv.sum_comp (Equiv.addRight j) (fun i : ZMod n => (i.val : ℤ))
  rw [h]
  ring

local notation "G" => Multiplicative (ZMod n)
local notation "T" => Rep.trivial ℤ G ℤ

/-- The ordinary integral positive carry cocycle. -/
def cyclicOrdinaryCarry : cocycles₂ T :=
  ⟨fun z => cyclicCarry z.1.toAdd z.2.toAdd, by
    apply (mem_cocycles₂_iff _).mpr
    intro g h j
    exact cyclicCarry_cocycle g.toAdd h.toAdd j.toAdd⟩

/-- The constructed cup sends a bar generator to the inverse element's representative. -/
theorem cyclicCarry_negative_cup (i : ZMod n) :
    tateTwoExtensionMap T (cyclicOrdinaryCarry n) (-2)
      (tateScalarGenerator ℤ G (Multiplicative.ofAdd i)) =
        tateInvariantClass T ⟨((-i).val : ℤ), fun _ => rfl⟩ := by
  rw [tateTwoExtensionMap_generator]
  apply congrArg (tateInvariantClass T)
  apply Subtype.ext
  change (∑ h : G, cyclicCarry h.toAdd (-i)) = _
  exact (Equiv.sum_comp Multiplicative.toAdd (fun h => cyclicCarry h (-i))).trans
    (cyclicCarry_sum n (-i))

/-- Modulo norms, the positive carry cup has the negative scalar representative. -/
theorem cyclicCarry_negative_cup_sign (i : ZMod n) :
    tateTwoExtensionMap T (cyclicOrdinaryCarry n) (-2)
      (tateScalarGenerator ℤ G (Multiplicative.ofAdd i)) =
        -tateInvariantClass T ⟨(i.val : ℤ), fun _ => rfl⟩ := by
  rw [cyclicCarry_negative_cup, eq_neg_iff_add_eq_zero, ← map_add]
  apply (tateInvariantClass_eq_zero_iff T _).mpr
  refine ⟨cyclicCarry i (-i), ?_⟩
  have h := cyclicCarry_mul i (-i)
  simp only [add_neg_cancel, ZMod.val_zero, Nat.cast_zero, sub_zero] at h
  change (∑ g : G, (Rep.trivial ℤ G ℤ).ρ g) (cyclicCarry i (-i)) = _
  simp only [LinearMap.sum_apply]
  change (∑ _ : G, cyclicCarry i (-i)) = ((-i).val : ℤ) + i.val
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_multiplicative, ZMod.card]
  exact (mul_comm _ _).trans (h.trans (add_comm _ _))

end LocalClassFieldTheory
