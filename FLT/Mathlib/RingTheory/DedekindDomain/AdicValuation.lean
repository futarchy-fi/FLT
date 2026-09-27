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
