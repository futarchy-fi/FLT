/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.AdicCompletion.PowerQuotients

/-!
# Character equality from ideal-power quotients

A uniform choice between two characters at every ideal-power quotient determines
the character over an adically separated ring.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- A character that is uniformly trivial or equal to a fixed character modulo
every ideal power is trivial or equal to that character. -/
theorem character_eq_one_or_of_power_quotients
    {G O : Type*} [Group G] [CommRing O]
    (I : Ideal O) [IsHausdorff I O] (ψ χ : G →* Oˣ)
    (hlevels :
      (∀ (n : ℕ) (g : G), Ideal.Quotient.mk (I ^ n) (ψ g : O) = 1) ∨
      (∀ (n : ℕ) (g : G), Ideal.Quotient.mk (I ^ n) (ψ g : O) =
        Ideal.Quotient.mk (I ^ n) (χ g : O))) :
    ψ = 1 ∨ ψ = χ := by
  rcases hlevels with h | h
  · left
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply eq_of_all_power_quotients I
    intro n
    simpa using h n g
  · right
    apply MonoidHom.ext
    intro g
    apply Units.ext
    exact eq_of_all_power_quotients I (fun n ↦ h n g)

end ThreeAdicPlan
