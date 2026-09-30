/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacter
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Inertia transitivity on roots of a uniformizer

Eisenstein irreducibility over each finite inertia fixed field gives transitivity.
This holds for every positive root degree, including the residue characteristic.
-/

@[expose] public section

open NumberField Polynomial IsLocalRing

namespace LocalRoot

/-- A uniformizer binomial is Eisenstein over a DVR. -/
theorem uniformizer_binomial_eisenstein {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) :
    (X ^ n - C π).IsEisensteinAt (maximalIdeal R) := by
  apply (monic_X_pow_sub_C π hn.ne').isEisensteinAt_of_mem_of_notMem
    (maximalIdeal.isMaximal R).ne_top
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    simp only [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right (Nat.ne_of_lt hi)]
    split_ifs
    · simpa using (maximalIdeal R).neg_mem hπ.not_isUnit
    · simp
  · rw [coeff_sub, coeff_X_pow, coeff_C]
    simp only [Ne.symm hn.ne', ↓reduceIte, zero_sub]
    rw [Ideal.neg_mem_iff, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    rintro ⟨t, ht⟩
    have he : 1 = π * t := by
      apply mul_left_cancel₀ hπ.ne_zero
      simpa [pow_two, mul_assoc] using ht
    exact hπ.not_isUnit (isUnit_iff_dvd_one.mpr ⟨t, he⟩)

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv

set_option maxHeartbeats 1000000 in
-- Integral-closure towers and finite Galois instances need extra elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- A base uniformizer stays a uniformizer in every finite inertia fixed field. -/
theorem uniformizer_irreducible_inertiaField
    (L : IntermediateField Kv Ω) [FiniteDimensional Kv L] [IsGalois Kv L]
    (E : IntermediateField Kv L)
    (hE : E = IntermediateField.fixedField
      ((maximalIdeal (IntegralClosure O L)).inertia Gal(L/Kv)))
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    Irreducible (algebraMap O (IntegralClosure O E) π) := by
  let D := IntegralClosure O E
  let p := maximalIdeal O
  let q := maximalIdeal D
  have : FiniteDimensional Kv E := FiniteDimensional.left Kv E L
  let : Module.Finite O D := by
    change Module.Finite O (integralClosure O E)
    exact IsIntegralClosure.finite O Kv E (integralClosure O E)
  let : IsDedekindDomain D := by
    change IsDedekindDomain (integralClosure O E)
    exact IsIntegralClosure.isDedekindDomain O Kv E (integralClosure O E)
  let : FaithfulSMul O D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro r s hrs
    apply Subtype.ext
    apply (algebraMap Kv E).injective
    exact congrArg Subtype.val hrs
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have he : q.ramificationIdx O = 1 := finiteInertiaField_ramificationIndex_one v L E hE
  have hmap : Ideal.map (algebraMap O D) p = q := by
    have hfac := Ideal.map_algebraMap_eq_finsetProd_pow (R := D) hp
    dsimp only [q] at he ⊢
    simpa [IsLocalRing.primesOver_eq D hp, he] using hfac
  let : q.LiesOver p := by dsimp only [q, p]; infer_instance
  have hq : q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp q
  let : IsDiscreteValuationRing D := { not_a_field' := hq }
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  change q = _
  rw [← hmap]
  rw [show p = Ideal.span {π} from
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer K v hπ]
  rw [Ideal.map_span, Set.image_singleton]

set_option maxHeartbeats 1000000 in
-- Integral-closure towers and finite Galois instances need extra elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- Finite local inertia acts transitively on roots of a uniformizer. -/
theorem finite_inertia_transitive
    (L : IntermediateField Kv Ω) [FiniteDimensional Kv L] [IsGalois Kv L]
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {n : ℕ} (hn : 0 < n) {α β : L}
    (hα : α ^ n = algebraMap O L π) (hβ : β ^ n = algebraMap O L π) :
    ∃ σ : (maximalIdeal (IntegralClosure O L)).inertia Gal(L/Kv), σ.1 α = β := by
  let H := (maximalIdeal (IntegralClosure O L)).inertia Gal(L/Kv)
  let E : IntermediateField Kv L := IntermediateField.fixedField H
  let : IsInertiaField Kv L (maximalIdeal (IntegralClosure O L)) E :=
    { toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/Kv) Kv L H }
  have : IsGaloisGroup H E L := inferInstance
  have : FiniteDimensional Kv E := FiniteDimensional.left Kv E L
  let D := IntegralClosure O E
  let : IsFractionRing D E := by
    change IsFractionRing (integralClosure O E) E
    exact integralClosure.isFractionRing_of_finite_extension Kv E
  let : IsDedekindDomain D := by
    change IsDedekindDomain (integralClosure O E)
    exact IsIntegralClosure.isDedekindDomain O Kv E (integralClosure O E)
  let : (maximalIdeal D).LiesOver (maximalIdeal O) := inferInstance
  let : IsDiscreteValuationRing D :=
    { not_a_field' := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field O) (maximalIdeal D) }
  let p : D[X] := X ^ n - C (algebraMap O D π)
  have hpm : p.Monic := monic_X_pow_sub_C _ hn.ne'
  have hpi : Irreducible p :=
    (uniformizer_binomial_eisenstein
      (uniformizer_irreducible_inertiaField v L E rfl hπ) hn).irreducible
      inferInstance hpm.isPrimitive (by simpa [p] using hn)
  let f : E[X] := p.map (algebraMap D E)
  have hfi : Irreducible f := (hpm.irreducible_iff_irreducible_map_fraction_map).mp hpi
  have hfm : f.Monic := hpm.map _
  have hf (x : L) (hx : x ^ n = algebraMap O L π) : aeval x f = 0 := by
    simpa [f, p, IsScalarTower.algebraMap_apply O E L,
      ← IsScalarTower.algebraMap_apply O D E] using sub_eq_zero.mpr hx
  have hmin : minpoly E β = f := (minpoly.eq_of_irreducible_of_monic hfi (hf β hβ) hfm).symm
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (IsAlgebraic.of_finite E β)
    (show aeval α (minpoly E β) = 0 by rw [hmin]; exact hf α hα)
  obtain ⟨τ, hτ⟩ := (IsGaloisGroup.mulEquivAlgEquiv H E L).surjective σ
  exact ⟨τ, by change (IsGaloisGroup.mulEquivAlgEquiv H E L τ) α = β; rw [hτ, hσ]⟩

set_option maxHeartbeats 1000000 in
-- Integral-closure towers and finite Galois instances need extra elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- Local absolute inertia acts transitively on the roots of a uniformizer. -/
theorem inertia_transitive
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {n : ℕ} (hn : 0 < n) {α β : Ω}
    (hα : α ^ n = algebraMap Kv Ω π.1) (hβ : β ^ n = algebraMap Kv Ω π.1) :
    ∃ σ : localInertiaGroup v, σ.1 α = β := by
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((ContinuousSMulDiscrete.isOpen_stabilizer (Field.absoluteGaloisGroup Kv) α).inter
      (ContinuousSMulDiscrete.isOpen_stabilizer (Field.absoluteGaloisGroup Kv) β))
    ⟨one_mem _, one_mem _⟩
  let L : IntermediateField Kv Ω := IntermediateField.fixedField N.1.1
  let : FiniteDimensional Kv L := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup (Field.absoluteGaloisGroup Kv))]
    exact N.isOpen'
  let : IsGalois Kv L := by
    rw [← InfiniteGalois.normal_iff_isGalois]
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup (Field.absoluteGaloisGroup Kv))]
    infer_instance
  let a : L := ⟨α, fun g ↦ (hN g.2).1⟩
  let b : L := ⟨β, fun g ↦ (hN g.2).2⟩
  obtain ⟨τ, hτ⟩ := finite_inertia_transitive v L hπ hn
    (show a ^ n = algebraMap O L π from Subtype.ext hα)
    (show b ^ n = algebraMap O L π from Subtype.ext hβ)
  have hmap := map_localInertiaGroup_eq_finiteInertia (v := v) N
  have ht : τ.1 ∈ Subgroup.map (AlgEquiv.restrictNormalHom L) (localInertiaGroup v) := by
    rw [hmap]
    exact τ.2
  obtain ⟨σ, hσ, hστ⟩ := ht
  refine ⟨⟨σ, hσ⟩, ?_⟩
  have he := congrArg (algebraMap L Ω) hτ
  rw [← hστ] at he
  exact (AlgEquiv.restrictNormal_commutes σ L a).symm.trans he

end LocalRoot
