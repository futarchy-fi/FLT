/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorAdicCriterion
public import FLT.Mazur.IdealTensorPresentationCriterion
public import FLT.Mazur.TensorInjectivityFiniteLength
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The local maximal-ideal tensor criterion for flatness

For a local map of Noetherian local rings and a module finite over the
target, injectivity for the base maximal ideal implies flatness over the
base. A free presentation, finite-length dévissage, and Artin-Rees give the
proof; the module is not required to be finite over the base.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalIdealTensorCriterion
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Ideals containing a positive maximal-ideal power have finite-length quotients. -/
theorem quotient_finiteLength (J : Ideal R) (n : ℕ)
    (h : IsLocalRing.maximalIdeal R ^ n ≤ J) : IsFiniteLength R (R ⧸ J) := by
  let _ : Ring.KrullDimLE 0 (R ⧸ J) := Ring.krullDimLE_zero_iff.mpr fun P hP ↦ by
    let _ := hP
    let _ := hP.comap (Ideal.Quotient.mk J)
    have hle : J ≤ P.comap (Ideal.Quotient.mk J) := by
      simpa only [Ideal.mk_ker] using Ideal.ker_le_comap (Ideal.Quotient.mk J)
    have he := (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le Ideal.IsPrime.ne_top'
      (Ideal.IsPrime.le_of_pow_le (h.trans hle))
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P
    change (P.comap (Ideal.Quotient.mk J)).IsMaximal
    rw [← he]
    infer_instance
  let _ : IsArtinianRing (R ⧸ J) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let _ : IsArtinian R (R ⧸ J) :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ J) Ideal.Quotient.mk_surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- A fixed free presentation, sealed to keep its kernel from unfolding finite sums. -/
irreducible_def presentation (M : Type*) [AddCommGroup M] [Module R M] :
    (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- This free presentation is onto without any finite-generation hypothesis. -/
theorem presentation_surjective (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Surjective (presentation (R := R) M) := by
  rw [presentation_def]
  exact Finsupp.linearCombination_id_surjective R M

variable {S M : Type*} [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Finite S M]

include S in
/-- A presentation injective on the closed fiber has a flat cokernel in this local setting. -/
theorem flat_of_presentation_residue
    {P N : Type*} [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [Module.Flat R N] (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    (hres : Function.Injective (f.lTensor (IsLocalRing.ResidueField R))) :
    Module.Flat R M := by
  apply IdealTensorAdicCriterion.flat_of_adic_tests (S := S) (M := M)
    (IsLocalRing.maximalIdeal R)
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S)))
  intro J n
  let K := J ⊔ IsLocalRing.maximalIdeal R ^ (n + 1)
  have hlen : IsFiniteLength R (R ⧸ K) := quotient_finiteLength K (n + 1) le_sup_right
  have hquot := TensorInjectivityFiniteLength.injective_of_closedFiber f hres hlen
  have hK := IdealTensorPresentationCriterion.ideal_injective f q he hq K hquot
  exact (AlgebraTensorModule.rid R S M).injective.comp
    ((K.subtype.lTensor_inj_iff_rTensor_inj M).mpr hK)


/-- The single maximal-ideal tensor test proves genuine flatness of the whole module. -/
theorem flat_of_maximalIdeal_injective
    (h : Function.Injective
      (ModuleIdealTensor.inclusion (S := S) (M := M) (IsLocalRing.maximalIdeal R))) :
    Module.Flat R M := by
  generalize hqdef : presentation (R := R) M = q
  let f : q.ker →ₗ[R] (M →₀ R) := q.ker.subtype
  have hq : Function.Surjective q := by
    rw [← hqdef]
    exact presentation_surjective M
  have he : Function.Exact f q := LinearMap.exact_subtype_ker_map q
  have hm : Function.Injective ((IsLocalRing.maximalIdeal R).subtype.rTensor M) := by
    apply ((IsLocalRing.maximalIdeal R).subtype.lTensor_inj_iff_rTensor_inj M).mp
    intro x y hxy
    apply h
    exact congrArg (AlgebraTensorModule.rid R S M) hxy
  apply flat_of_presentation_residue (R := R) (S := S)
    (P := q.ker) (N := M →₀ R) f q he hq
  apply IdealTensorPresentationCriterion.quotient_injective
    (R := R) (P := q.ker) (N := M →₀ R) (f := f) (q := q)
    he hq q.ker.subtype_injective (IsLocalRing.maximalIdeal R)
  exact hm

end FLT.Mazur.LocalIdealTensorCriterion
