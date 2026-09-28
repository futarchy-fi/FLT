/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.DedekindDomain.Completion.Different
public import FLT.Mathlib.RingTheory.DifferentBaseRing
public import FLT.NumberField.DifferentExponentBounds

/-!
# The absolute different of a number-field completion

An integral basis gives compatibility of the absolute different with completion.
The multiplicity of the completed maximal ideal is the global different exponent.
-/

@[expose] public noncomputable section

open Module Algebra IsDedekindDomain.HeightOneSpectrum UniqueFactorizationMonoid

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace NumberField

variable (L : Type*) [Field L] [NumberField L]

/-- Finite-place completions of number fields have characteristic zero. -/
instance completionCharZero (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    CharZero (v.adicCompletion L) := by
  constructor
  intro m n h
  apply Nat.cast_injective (R := L)
  apply (algebraMap L (v.adicCompletion L)).injective
  simpa only [map_natCast] using h

/-- The completed integer extension is torsion-free over the completed base integers. -/
instance completionIntegersTorsionFree
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 L)) :
    Module.IsTorsionFree (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) := by
  let : IsScalarTower (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  let : FaithfulSMul (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) :=
    FaithfulSMul.of_field_isFractionRing _ _ (v.adicCompletion ℚ) (w.1.adicCompletion L)
  infer_instance

/-- Using the integers of `ℚ` instead of `ℤ` leaves the absolute different unchanged. -/
theorem differentIdeal_ratIntegers_eq :
    differentIdeal (𝓞 ℚ) (𝓞 L) = differentIdeal ℤ (𝓞 L) := by
  apply differentIdeal_eq_of_algebraMap_range_eq (𝓞 ℚ) ℤ ℚ L (𝓞 L)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Rat.ringOfIntegersEquiv z, Rat.ringOfIntegersEquiv_apply_coe z⟩
  · rintro ⟨z, rfl⟩
    exact ⟨Rat.ringOfIntegersEquiv.symm z, Rat.ringOfIntegersEquiv_symm_apply_coe z⟩

/-- The integral basis also spans the integers when coefficients are written as `𝓞 ℚ`. -/
theorem span_integralBasis_ratIntegers :
    (1 : Submodule (𝓞 L) L).restrictScalars (𝓞 ℚ) =
      Submodule.span (𝓞 ℚ) (Set.range (integralBasis L)) := by
  apply le_antisymm
  · intro x hx
    exact Submodule.span_subset_span ℤ (𝓞 ℚ) _
      ((mem_span_integralBasis (K := L)).mpr (Submodule.mem_one.mp hx))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_one.mpr ⟨RingOfIntegers.basis L i, (integralBasis_apply L i).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- The absolute different extends to the different of the completed extension
of number fields over the completed rationals. -/
theorem map_differentIdeal_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 L)) :
    (differentIdeal ℤ (𝓞 L)).map (algebraMap (𝓞 L) (w.1.adicCompletionIntegers L)) =
      differentIdeal (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) := by
  let : IsScalarTower (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  let : FaithfulSMul (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) :=
    FaithfulSMul.of_field_isFractionRing _ _ (v.adicCompletion ℚ) (w.1.adicCompletion L)
  rw [← differentIdeal_ratIntegers_eq L]
  exact IsDedekindDomain.HeightOneSpectrum.map_differentIdeal_completion
    (𝓞 ℚ) ℚ L (𝓞 L) v (integralBasis L) (span_integralBasis_ratIntegers L) w

/-- The exponent of the local different equals the exponent of the global
different at the chosen prime. -/
theorem count_differentIdeal_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 L)) :
    (normalizedFactors (differentIdeal (v.adicCompletionIntegers ℚ)
      (w.1.adicCompletionIntegers L))).count (w.1.completionIdeal L) =
        differentExponentAt L w.1.asIdeal := by
  rw [← map_differentIdeal_completion L v w, count_normalizedFactors_map_completion]
  rfl

end NumberField
