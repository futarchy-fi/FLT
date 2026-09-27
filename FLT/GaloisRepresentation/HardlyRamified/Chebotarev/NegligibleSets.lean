/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Removing negligible sets of prime ideals

Leaf D2 of `docs/CHEBOTAREV_PLAN.md`. The normalization is logarithmic, not
Mathlib's all-prime-ideal normalization. Since Z2 is not yet available on this
branch, `logDensity_diff` takes prime-norm summability for `s > 1` explicitly.
The finite-set and large-norm results need no such hypothesis.
-/

@[expose] public section

noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Topology

namespace GaloisRepresentation.Chebotarev

/-- Nonzero prime ideals of the ring of integers. -/
@[nolint unusedArguments]
abbrev Prime (K : Type*) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

/-- The absolute norm of a prime ideal. -/
def norm {K : Type*} [Field K] [NumberField K] (v : Prime K) : ℕ :=
  v.asIdeal.absNorm

/-- The logarithmic normalization at the pole `s = 1`. -/
def ell (s : ℝ) : ℝ := Real.log (1 / (s - 1))

/-- The prime-ideal sum over a set. -/
abbrev ps {K : Type*} [Field K] [NumberField K] (T : Set (Prime K)) (s : ℝ) : ℝ :=
  NumberField.Set.primeIdealZetaSum T s

/-- Logarithmic Dirichlet density of a set of prime ideals. -/
def LogDensity {K : Type*} [Field K] [NumberField K]
    (T : Set (Prime K)) (d : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ ps T s / ell s) (𝓝[>] 1) (𝓝 d)

/-- The logarithmic normalizer tends to infinity from the right of one. -/
theorem tendsto_ell_atTop : Tendsto ell (𝓝[>] 1) atTop := by
  have hsub : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_nhdsWithin_of_tendsto_nhds
        (continuous_id.tendsto (1 : ℝ))).sub_const 1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr hs
  change Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] 1) atTop
  simpa only [one_div, Function.comp_def] using
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hsub)

/-- A bounded function vanishes after logarithmic normalization. -/
theorem tendsto_div_ell_of_isBigO {f : ℝ → ℝ}
    (hf : Asymptotics.IsBigO (𝓝[>] (1 : ℝ)) f (fun _ ↦ (1 : ℝ))) :
    Tendsto (fun s ↦ f s / ell s) (𝓝[>] 1) (𝓝 0) :=
  (hf.trans_isLittleO
    ((Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
      tendsto_ell_atTop)).tendsto_div_nhds_zero

variable {K : Type*} [Field K] [NumberField K]

/-- Finite prime sets have bounded prime sums near one. -/
theorem primeSum_isBigO_of_finite {T : Set (Prime K)} (hT : T.Finite) :
    Asymptotics.IsBigO (𝓝[>] (1 : ℝ)) (ps T) (fun _ ↦ (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (T.ncard : ℝ) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (NumberField.Set.primeIdealZetaSum_nonneg T s),
    norm_one, mul_one] using
    NumberField.Set.primeIdealZetaSum_le_card_of_finite hT (le_of_lt (lt_trans zero_lt_one hs))

/-- Finite sets have logarithmic density zero. -/
theorem logDensity_zero_of_finite {T : Set (Prime K)} (hT : T.Finite) :
    LogDensity T 0 :=
  tendsto_div_ell_of_isBigO (primeSum_isBigO_of_finite hT)

/-- Removing a set with bounded prime sum preserves logarithmic density.
The summability hypothesis is the input supplied by leaf Z2. -/
theorem logDensity_diff
    (hsum : ∀ s : ℝ, 1 < s → Summable (fun v : Prime K ↦ (norm v : ℝ) ^ (-s)))
    (T U : Set (Prime K)) (d : ℝ) (hT : LogDensity T d)
    (hU : Asymptotics.IsBigO (𝓝[>] (1 : ℝ)) (ps U) (fun _ ↦ (1 : ℝ))) :
    LogDensity (T \ U) d := by
  have hbound : Asymptotics.IsBigO (𝓝[>] (1 : ℝ)) (ps (T ∩ U)) (fun _ ↦ (1 : ℝ)) := by
    obtain ⟨c, hc⟩ := hU.bound
    refine Asymptotics.IsBigO.of_bound c ?_
    filter_upwards [hc, self_mem_nhdsWithin] with s hs h1
    have hle : ps (T ∩ U) s ≤ ps U s := by
      dsimp only [ps]
      simp only [NumberField.Set.primeIdealZetaSum_def]
      exact Summable.tsum_le_tsum_of_inj
        (fun v : ↥(T ∩ U) ↦ (⟨v.1, v.2.2⟩ : U))
        (fun _ _ h ↦ Subtype.ext (congrArg (fun v : U ↦ v.val) h))
        (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl)
        ((hsum s h1).subtype (fun v ↦ v ∈ T ∩ U))
        ((hsum s h1).subtype (fun v ↦ v ∈ U))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (NumberField.Set.primeIdealZetaSum_nonneg (T ∩ U) s)]
    exact hle.trans ((le_abs_self _).trans hs)
  have hlim := hT.sub (tendsto_div_ell_of_isBigO hbound)
  rw [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [← sub_div]
  congr 1
  have hdecomp : ps T s = ps (T \ U) s + ps (T ∩ U) s := by
    have hdisj : Disjoint (T \ U) (T ∩ U) := by
      exact Set.disjoint_left.mpr fun _ h1 h2 ↦ h1.2 h2.2
    have heq : (T \ U) ∪ (T ∩ U) = T := by ext v; simp
    dsimp only [ps]
    simp only [NumberField.Set.primeIdealZetaSum_def]
    conv_lhs => rw [← heq]
    exact Summable.tsum_union_disjoint hdisj
      ((hsum s hs).subtype (fun v ↦ v ∈ T \ U))
      ((hsum s hs).subtype (fun v ↦ v ∈ T ∩ U))
  exact sub_eq_iff_eq_add.mpr hdecomp

/-- Positive logarithmic density supplies a prime outside any finite set
and above any prescribed norm bound. -/
theorem exists_norm_ge_of_logDensity_pos
    (T : Set (Prime K)) (d : ℝ) (hd : 0 < d) (hT : LogDensity T d)
    (S : Finset (Prime K)) (N : ℕ) :
    ∃ v ∈ T, v ∉ S ∧ N ≤ norm v := by
  classical
  by_contra h
  have hsmall : {v : Prime K | norm v ≤ N}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le N).preimage HeightOneSpectrum.asIdeal_injective.injOn
  have hfinite : T.Finite := by
    apply (S.finite_toSet.union hsmall).subset
    intro v hv
    by_cases hS : v ∈ S
    · exact Or.inl hS
    · exact Or.inr (le_of_lt (lt_of_not_ge fun hN ↦ h ⟨v, hv, hS, hN⟩))
  have : d = 0 := tendsto_nhds_unique hT (logDensity_zero_of_finite hfinite)
  exact hd.ne' this

end GaloisRepresentation.Chebotarev
