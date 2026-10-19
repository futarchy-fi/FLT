/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# A discrete valuation model in a prescribed finite separable extension

Localize the integral closure at a maximal ideal above the original closed
point. Realize that localization inside the given extension field itself.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteExtensionDVRModel
open IsLocalRing
variable (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Module.Finite K L] [Algebra.IsSeparable K L]

include K in
/-- The prescribed extension admits a DVR model over the original local ring. -/
theorem exists_model :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S) (_ : Algebra S L) (_ : IsScalarTower R S L)
      (_ : IsFractionRing S L), IsLocalHom (algebraMap R S) := by
  let C := integralClosure R L
  let _ : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain R K L C
  let _ : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension R K L C
  have hinj : Function.Injective (algebraMap R C) :=
    algebraMap_injective_of_field_isFractionRing R C K L
  let _ : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hinj
  obtain ⟨Q, hQ, hQR⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (maximalIdeal R)
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  let _ := hQ
  have hQ0 : Q ≠ ⊥ := by
    intro he
    have hm : maximalIdeal R = ⊥ := by
      rw [← hQR, he, Ideal.under_def, Ideal.comap_bot_of_injective _ hinj]
    exact (IsDiscreteValuationRing.not_a_field R) hm
  let S := Localization.subalgebra L Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let _ : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ0 S
  let _ : Algebra R S := (algebraMap C S).comp (algebraMap R C) |>.toAlgebra
  let _ : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap R L x = algebraMap S L (algebraMap C S (algebraMap R C x))
    rw [← IsScalarTower.algebraMap_apply C S L, ← IsScalarTower.algebraMap_apply R C L]
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  apply ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq R C S, ← Ideal.comap_comap]
  change ((maximalIdeal S).under C).under R = maximalIdeal R
  rw [IsLocalization.AtPrime.under_maximalIdeal S Q, hQR]

end FLT.Mazur.FiniteExtensionDVRModel
