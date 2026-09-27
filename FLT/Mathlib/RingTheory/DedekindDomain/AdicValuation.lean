/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Adic Valuation

Material destined for Mathlib.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

-- TODO upstream
open IsDedekindDomain

instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense :=
    -- `adicCompletion` is now a one-field structure (not defeq to `Completion`), so use the
    -- mathlib-provided dense range of `algebraMap K → adicCompletion` and `K`'s countability.
    ⟨Set.range (algebraMap K (v.adicCompletion K)),
      Set.countable_range _, denseRange_algebraMap K v⟩

lemma intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_if_neg _ hnz, Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

/-- A height one prime of `B` lies over its pullback to `A`. -/
instance liesOver_under {A : Type*} [CommRing A] [IsDedekindDomain A] {B : Type*} [CommRing B]
    [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B] (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (under A w).asIdeal :=
  ⟨rfl⟩

/-- `adicCompletion.equiv` as a `K`-algebra isomorphism onto the underlying completion. -/
noncomputable def adicCompletion.algEquiv
    {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (v : HeightOneSpectrum A) :
    v.adicCompletion K ≃ₐ[K] (v.valuation K).Completion :=
  AlgEquiv.ofRingEquiv (f := adicCompletion.equiv K v)
    fun x => algebraMap_adicCompletion_toCompletion A K v x

open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
/-- The multiplicity of a principal fractional ideal is the negative logarithm
of its adic valuation, including the conventional value zero at the zero function. -/
theorem count_spanSingleton_eq_neg_log (v : HeightOneSpectrum R) (f : K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ f) =
      -WithZero.log (v.valuation K f) := by
  have hreg (a : R) (ha : a ≠ 0) :
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) =
        -WithZero.log (v.valuation K (algebraMap R K a)) := by
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
      (by simpa using ha), v.valuation_of_algebraMap, v.intValuation_if_neg ha,
      WithZero.log_exp, neg_neg]
  by_cases hf : f = 0
  · simp [hf, FractionalIdeal.count_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by intro ha; simp [ha] at hf
  have hKa : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha0
  have hKb : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul K v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hKa)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hKb)),
    FractionalIdeal.count_inv, hreg a ha0, hreg b hb0,
    map_div₀, WithZero.log_div ((map_ne_zero _).mpr hKa) ((map_ne_zero _).mpr hKb)]
  ring

end IsDedekindDomain.HeightOneSpectrum

open WithZero

namespace Valuation
variable {K : Type*} [Field K]
/-- Equivalent surjective integer-valued valuations on a field agree exactly. -/
theorem eq_of_isEquiv_of_surjective (v w : Valuation K ℤᵐ⁰)
    (h : v.IsEquiv w) (hv : Function.Surjective v) (hw : Function.Surjective w) : v = w := by
  obtain ⟨u, hu⟩ := hv (exp (1 : ℤ))
  obtain ⟨t, ht⟩ := hw (exp (1 : ℤ))
  have hu0 : u ≠ 0 := by
    intro he
    rw [he, map_zero] at hu
    exact exp_ne_zero hu.symm
  have ht0 : t ≠ 0 := by
    intro he
    rw [he, map_zero] at ht
    exact exp_ne_zero ht.symm
  have hwu0 : w u ≠ 0 := (map_ne_zero w).mpr hu0
  have hvt0 : v t ≠ 0 := (map_ne_zero v).mpr ht0
  let a := log (w u)
  let b := log (v t)
  have ha : 0 < a := by
    have hh : 1 < w u := by
      rw [← not_le, ← map_one w, ← h u 1, map_one, hu]
      exact not_le.mpr (exp_lt_exp.mpr zero_lt_one)
    simpa only [log_one] using (log_lt_log one_ne_zero hwu0).mpr hh
  have hb : 0 < b := by
    have hh : 1 < v t := by
      rw [← not_le, ← map_one v, h t 1, map_one, ht]
      exact not_le.mpr (exp_lt_exp.mpr zero_lt_one)
    simpa only [log_one] using (log_lt_log one_ne_zero hvt0).mpr hh
  have he : v (u ^ b) = v t := by
    rw [map_zpow₀, hu, ← exp_zsmul, zsmul_eq_mul, mul_one]
    exact exp_log hvt0
  have he' := h.eq_iff.mp he
  rw [map_zpow₀, ← exp_log hwu0, ← exp_zsmul, ht, exp_inj, zsmul_eq_mul] at he'
  have ha1 : a = 1 := by
    change b * a = 1 at he'
    nlinarith
  have hwu : w u = exp (1 : ℤ) := by rw [← exp_log hwu0]; exact congrArg exp ha1
  ext f
  by_cases hf : f = 0
  · simp [hf]
  have hvf : v f ≠ 0 := (map_ne_zero v).mpr hf
  have he : v (u ^ log (v f)) = v f := by
    rw [map_zpow₀, hu, ← exp_zsmul, zsmul_eq_mul, mul_one, Int.cast_id, exp_log hvf]
  have he' := h.eq_iff.mp he
  rw [map_zpow₀, hwu, ← exp_zsmul, zsmul_eq_mul, mul_one, Int.cast_id, exp_log hvf] at he'
  exact he'
end Valuation
open IsDedekindDomain
namespace IsDedekindDomain.HeightOneSpectrum
variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
/-- A surjective integer-valued valuation which is integral on a Dedekind
ring and centered at p is the normalized p-adic valuation. -/
theorem valuation_eq_of_center (p : HeightOneSpectrum R) (w : Valuation K ℤᵐ⁰)
    (hw : Function.Surjective w)
    (hR : ∀ a : R, w (algebraMap R K a) ≤ 1)
    (hM : ∀ a : R, w (algebraMap R K a) < 1 ↔ a ∈ p.asIdeal) :
    p.valuation K = w := by
  have hle : (p.valuation K).valuationSubring ≤ w.valuationSubring := by
    intro x hx
    obtain ⟨a, d, he⟩ := p.exists_primeCompl_mul_eq_of_integer x hx
    have hd : w (algebraMap R K d) = 1 := by
      apply le_antisymm (hR d)
      apply le_of_not_gt
      intro hd
      exact d.property ((hM d).mp hd)
    have hh := congrArg w he
    rw [map_mul, hd, mul_one] at hh
    change w x ≤ 1
    rw [hh]
    exact hR a
  have hne : w.valuationSubring ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hw (exp (1 : ℤ))
    intro he
    have hh : x ∈ w.valuationSubring := he ▸ Set.mem_univ x
    change w x ≤ 1 at hh
    rw [hx] at hh
    exact not_le.mpr (exp_lt_exp.mpr (by norm_num : (0 : ℤ) < 1)) hh
  have heq := ValuationSubring.eq_of_le_of_ne_top _ hle hne
  exact Valuation.eq_of_isEquiv_of_surjective _ _
    ((Valuation.isEquiv_iff_valuationSubring ..).mpr heq) (p.valuation_surjective K) hw
end IsDedekindDomain.HeightOneSpectrum
