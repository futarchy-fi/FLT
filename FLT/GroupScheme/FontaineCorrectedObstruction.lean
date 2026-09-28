/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineLowPrecisionObstruction
public import FLT.GroupScheme.FontaineWildObstruction
public import FLT.GroupScheme.LocalInertiaMaximum

/-!
# Fontaine's corrected obstruction and strict different bound

The unramified coefficient field supplies the low-precision obstruction.
For larger inertia displacement, an Eisenstein perturbation realizes the
forbidden critical value in an extension of the same degree. Together these
prove the corrected obstruction without an extension-existence hypothesis.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L] [IsGalois ℚ_[3] L]

/-- Fontaine's property fails below the different plus any nonidentity
displacement, with the original one-valuation-step correction. -/
theorem notFontainePropertyOfCorrectedCutoff
    (σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L)
    (hσ : σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L)) (m : ℚ) (hm : 0 < m)
    (hcut : m < normalizedDifferentExponent L + threeAdicDisplacementOrder L σ -
      1 / (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ)) :
    ¬ FontaineProperty (ThreeAdicIntegers L) m := by
  obtain ⟨c, hc, hbound, hmax, hprecision⟩ :=
    existsThreeAdicInertiaCriticalData L σ hσ m hm hcut
  obtain ⟨C, instRing, instDomain, instDvr, instAlgZ, instFinite, instAlgC,
    instTower, instFaithfulC, instFaithfulZ, instUnramified, pb, h3, hgen, hP,
    hdim, hres⟩ := existsThreeAdicEisensteinPresentation L
  obtain ⟨pc⟩ := existsThreeAdicCoefficientPowerBasis C
  by_cases hc1 : c = 1
  · subst c
    obtain ⟨τ, hτ, _⟩ := hmax
    have he : 1 < pb.dim := by
      rw [hdim]
      exact threeAdicRamificationGtOneOfNontrivialInertia L τ hτ
    have hD := threeAdicDifferentOrderLeRamificationSubOne L hbound
    have hepos : (0 : ℚ) <
        threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) :=
      Nat.cast_pos.mpr (threeAdicIdealOrder_three_pos L)
    have hm1 : m ≤ 1 := hprecision.trans (by
      simp only [Nat.add_sub_cancel]
      apply (div_le_iff₀ hepos).mpr
      simp only [one_mul]
      exact Nat.cast_le.mpr (hD.trans (Nat.sub_le _ _)))
    exact notFontainePropertyOfRamifiedPresentation L pb h3 hP he m hm1
  · exact notFontainePropertyOfWildPresentation L pc pb h3 hP hdim c
      (by omega) hbound hmax m hprecision

/-- Fontaine's property above three halves forces a strict different bound,
with the corrected obstruction supplied by the constructed extensions. -/
theorem normalizedDifferentExponentLtThreeHalvesOfFontaineProperty
    (hP : ∀ m : ℚ, (3 / 2 : ℚ) < m → FontaineProperty (ThreeAdicIntegers L) m) :
    normalizedDifferentExponent L < (3 / 2 : ℚ) := by
  apply normalizedDifferentExponentLtThreeHalvesOfCorrectedFontaineObstructions L hP
  exact notFontainePropertyOfCorrectedCutoff L

end ThreeAdicPlan
