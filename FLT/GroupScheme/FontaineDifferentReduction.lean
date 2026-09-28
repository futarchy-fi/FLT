/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineRootCriterion
public import FLT.GroupScheme.LocalDifferentConjugates

/-!
# Strict different bounds from Fontaine obstructions

These are conditional reductions, not a proof of Fontaine's ramification
theorem. The missing arithmetic input constructs an approximate root in an
extension admitting no embedding of the original field.

Write `d` for the normalized different exponent and `i(σ)` for a
displacement order. An obstruction at every positive `m < d + i(σ) - c`
turns the properties `P_m` for all `m > u` into `d + i(σ) - c ≤ u`.
If `d ≥ u` forces some `i(σ) > c`, this gives the strict bound `d < u`.

The correction is explicit: Fontaine, Invent. Math. 81 (1985), Proposition
1.5(ii), uses `c = 1/e`, where `e` is the ramification index. Using `c = 0`
requires a stronger obstruction theorem; it does not follow from that
proposition alone. The sum formula proves the positive-displacement input
for `c = 0`. No obstruction theorem is assumed as an axiom or an instance.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

omit [Algebra ℚ_[3] L] [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L] in
/-- If every positive precision below a threshold fails Fontaine's property,
then properties at all precisions above a nonnegative bound force the threshold
to be at most that bound. -/
theorem fontaineThresholdLeOfObstructions (u t : ℚ) (hu : 0 ≤ u)
    (hP : ∀ m : ℚ, u < m → FontaineProperty (ThreeAdicIntegers L) m)
    (hbad : ∀ m : ℚ, 0 < m → m < t →
      ¬ FontaineProperty (ThreeAdicIntegers L) m) : t ≤ u := by
  by_contra h
  have hut : u < t := lt_of_not_ge h
  obtain ⟨m, hum, hmt⟩ := exists_between hut
  exact hbad m (lt_of_le_of_lt hu hum) hmt (hP m hum)

/-- A corrected displacement obstruction implies a strict different bound
when a putative violation supplies a displacement larger than the correction.
Both the obstruction and the displacement condition are explicit hypotheses. -/
theorem normalizedDifferentExponentLtOfFontaineObstructions (u c : ℚ) (hu : 0 < u)
    (hP : ∀ m : ℚ, u < m → FontaineProperty (ThreeAdicIntegers L) m)
    (hlarge : u ≤ normalizedDifferentExponent L →
      ∃ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
        σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) ∧ c < threeAdicDisplacementOrder L σ)
    (hbad : ∀ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) → ∀ m : ℚ, 0 < m →
      m < normalizedDifferentExponent L + threeAdicDisplacementOrder L σ - c →
      ¬ FontaineProperty (ThreeAdicIntegers L) m) :
    normalizedDifferentExponent L < u := by
  by_contra h
  have hud : u ≤ normalizedDifferentExponent L := le_of_not_gt h
  obtain ⟨σ, hσ, hc⟩ := hlarge hud
  have hle := fontaineThresholdLeOfObstructions L u
    (normalizedDifferentExponent L + threeAdicDisplacementOrder L σ - c)
    hu.le hP (hbad σ hσ)
  linarith

/-- With no correction, the sum formula supplies the displacement needed
for strictness. The stronger obstruction hypothesis remains unproved here. -/
theorem normalizedDifferentExponentLtOfUncorrectedFontaineObstructions
    [Normal ℚ_[3] L] (u : ℚ) (hu : 0 < u)
    (hP : ∀ m : ℚ, u < m → FontaineProperty (ThreeAdicIntegers L) m)
    (hbad : ∀ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) → ∀ m : ℚ, 0 < m →
      m < normalizedDifferentExponent L + threeAdicDisplacementOrder L σ →
      ¬ FontaineProperty (ThreeAdicIntegers L) m) :
    normalizedDifferentExponent L < u := by
  apply normalizedDifferentExponentLtOfFontaineObstructions L u 0 hu hP
  · intro hud
    exact existsPositiveDisplacementOfDifferentPos L (lt_of_lt_of_le hu hud)
  · simpa only [sub_zero] using hbad

/-- The preceding conditional reduction at the finite-flat three-adic cutoff. -/
theorem normalizedDifferentExponentLtThreeHalvesOfFontaineObstructions
    [Normal ℚ_[3] L]
    (hP : ∀ m : ℚ, (3 / 2 : ℚ) < m → FontaineProperty (ThreeAdicIntegers L) m)
    (hbad : ∀ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) → ∀ m : ℚ, 0 < m →
      m < normalizedDifferentExponent L + threeAdicDisplacementOrder L σ →
      ¬ FontaineProperty (ThreeAdicIntegers L) m) :
    normalizedDifferentExponent L < (3 / 2 : ℚ) :=
  normalizedDifferentExponentLtOfUncorrectedFontaineObstructions L (3 / 2) (by norm_num) hP hbad

end ThreeAdicPlan
