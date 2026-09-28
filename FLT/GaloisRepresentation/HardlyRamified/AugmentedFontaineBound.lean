/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedDyadicDifferent
public import FLT.GaloisRepresentation.HardlyRamified.AugmentedGlobalDifferent

/-!
# The augmented discriminant bound from the local Fontaine hypothesis

Every prime containing three defines an extension of the chosen rational
three-adic place. The completed different bound therefore supplies the global
primewise input to the discriminant reduction; the dyadic input is already proved.
-/

@[expose] public noncomputable section

open NumberField

namespace ThreeAdicPlan

/-- Every prime containing three is the ideal of an extension of the chosen
rational three-adic place. -/
theorem exists_threeAdicPointFieldPlace_extension_of_three_mem
    {L : Type*} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [hPrime : P.IsPrime] (hP : (3 : 𝓞 L) ∈ P) :
    ∃ w : threeAdicPointFieldPlace.Extension (𝓞 L), w.1.asIdeal = P := by
  have hne : P ≠ ⊥ := by
    intro heq
    simp [heq] at hP
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨P, hPrime, hne⟩
  have hle : threeAdicPointFieldPlace.asIdeal ≤ P.under (𝓞 ℚ) := by
    rw [threeAdicPointFieldPlace_asIdeal, Ideal.span_singleton_le_iff_mem]
    change algebraMap (𝓞 ℚ) (𝓞 L) 3 ∈ P
    simpa only [map_ofNat] using hP
  have heq : w.under (𝓞 ℚ) = threeAdicPointFieldPlace := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (threeAdicPointFieldPlace.isMaximal.eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) hle).symm
  exact ⟨⟨w, heq⟩, rfl⟩

/-- Fontaine's local hypothesis bounds the normalized global different at
every augmented-field prime containing three. -/
theorem augmentedField_normalizedDifferent_lt_of_three_mem
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (P : Ideal (𝓞 (AugmentedField H))) [hPrime : P.IsPrime]
    (hP : (3 : 𝓞 (AugmentedField H)) ∈ P) :
    normalizedDifferentExponentAt (AugmentedField H) P < (3 / 2 : ℚ) := by
  obtain ⟨w, rfl⟩ := exists_threeAdicPointFieldPlace_extension_of_three_mem P hP
  exact augmentedField_normalizedDifferent_lt hF hs hD w

/-- The local Fontaine hypothesis implies the augmented discriminant estimate
for every simple object of category D. -/
theorem augmentedDiscriminantBound_of_fontaine
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    AugmentedDiscriminantBound H :=
  augmentedDiscriminantBound_of_three_bound hs hD
    (augmentedField_normalizedDifferent_lt_of_three_mem hF hs hD)

end ThreeAdicPlan
