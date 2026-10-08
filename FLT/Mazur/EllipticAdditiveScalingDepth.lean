/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticShortExtensionScaling

/-!
# Additive short equations require positive scaling

Both nonzero-weight coefficients of an additive short equation are nonunits.
A local extension preserves this property, so a saturated weighted depth cannot
have exponent zero. This applies to the explicit S2a extension witnesses.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Additive invariants force both short coefficients into the maximal ideal. -/
theorem short_additive_coefficients_mem (W : WeierstrassCurve R) [W.IsShortNF]
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (hd : W.Δ ∈ maximalIdeal R) (hc : W.c₄ ∈ maximalIdeal R) :
    W.a₄ ∈ maximalIdeal R ∧ W.a₆ ∈ maximalIdeal R := by
  have hn : ¬ (IsUnit W.a₄ ∨ IsUnit W.a₆) := by
    intro h
    rcases short_unit_discriminant_or_c₄ W h2 h3 h with h | h
    · exact hd h
    · exact hc h
  exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩

/-- A saturated weighted depth over a local extension of an additive equation is positive. -/
theorem short_additive_scaling_exponent_pos {S : Type*}
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) [IsLocalHom f] (W : WeierstrassCurve R) [W.IsShortNF]
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (hd : W.Δ ∈ maximalIdeal R) (hc : W.c₄ ∈ maximalIdeal R) (m : ℕ)
    (hs : addVal S (f W.a₄) = (4 * m : ℕ) ∨
      addVal S (f W.a₆) = (6 * m : ℕ)) : 0 < m := by
  obtain ⟨h4, h6⟩ := short_additive_coefficients_mem W h2 h3 hd hc
  by_contra hm
  have hm0 : m = 0 := by omega
  simp only [hm0, mul_zero, Nat.cast_zero] at hs
  rcases hs with hs | hs
  · exact h4 (IsLocalHom.map_nonunit (f := f) _ (addVal_eq_zero_iff.mp hs))
  · exact h6 (IsLocalHom.map_nonunit (f := f) _ (addVal_eq_zero_iff.mp hs))

end FLT.Mazur
