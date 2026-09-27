/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.HigherDegree
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.PrimeFibers
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.SubfieldSplitting
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# The contribution outside completely split fibers

Leaf B3 of `docs/CHEBOTAREV_PLAN.md`. Ramified fibers form a finite set;
every remaining nonsplit prime has residue degree at least two.
-/

@[expose] public section

noncomputable section

open Filter IsDedekindDomain NumberField
open scoped Topology

namespace GaloisRepresentation.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- Contraction of a nonzero prime to the base number field. -/
def primeBelow (w : Prime L) : Prime K :=
  ⟨w.asIdeal.under (𝓞 K), inferInstance, Ideal.IsIntegral.under_ne_bot _ w.ne_bot⟩

/-- The primes in a contraction fiber are the usual ideals lying over the base prime. -/
def primeBelowFiberEquiv (v : Prime K) :
    {w : Prime L // primeBelow K L w = v} ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg (·.asIdeal) w.2).symm⟩⟩
  invFun w := ⟨⟨w.1, w.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot w.1⟩,
    HeightOneSpectrum.asIdeal_injective (w.2.2.over).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Contraction has finite fibers. -/
theorem finite_primeBelow_fiber (v : Prime K) :
    {w : Prime L | primeBelow K L w = v}.Finite := by
  let := (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 L) v.asIdeal).to_subtype
  exact Set.finite_coe_iff.mp
    (Finite.of_equiv (v.asIdeal.primesOver (𝓞 L)) (primeBelowFiberEquiv K L v).symm)

/-- Only finitely many top primes ramify over the base field. -/
theorem finite_ramified_top :
    {w : Prime L | ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal}.Finite := by
  have hd : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd
  apply ((Ring.HasFiniteQuotients.finite_setOfPred_mem x hx0).preimage
    HeightOneSpectrum.asIdeal_injective.injOn).subset
  intro w hw
  have hdiv : w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    by_contra h
    exact hw (not_dvd_differentIdeal_iff.mp h)
  exact (Ideal.dvd_iff_le.mp hdiv) hx

/-- Only finitely many base primes ramify in the extension. -/
theorem finite_ramified : {v : Prime K | ¬ Unram K L v}.Finite := by
  apply ((finite_ramified_top K L).image (primeBelow K L)).subset
  intro v hv
  simp only [Unram, Algebra.IsUnramifiedIn, not_forall] at hv
  obtain ⟨w, hw, hl, hu⟩ := hv
  let := hw
  let := hl
  let w' : Prime L := ⟨w, hw, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot w⟩
  exact ⟨w', hu, HeightOneSpectrum.asIdeal_injective hl.over.symm⟩

/-- All fibers over ramified base primes form a finite set. -/
theorem finite_ramified_fibers :
    {w : Prime L | ¬ Unram K L (primeBelow K L w)}.Finite :=
  (finite_ramified K L).preimage' fun v _ ↦ finite_primeBelow_fiber K L v

variable [IsGalois K L]

/-- Reindexing primes above split primes by their base prime and fiber. -/
def splitPrimeEquiv :
    (Σ v : Split K L, v.1.asIdeal.primesOver (𝓞 L)) ≃
      ↥{w : Prime L | primeBelow K L w ∈ Split K L} where
  toFun x :=
    let w := (primeBelowFiberEquiv K L x.1.1).symm x.2
    ⟨w.1, by change primeBelow K L w.1 ∈ Split K L; rw [w.2]; exact x.1.2⟩
  invFun w := ⟨⟨primeBelow K L w.1, w.2⟩,
    (primeBelowFiberEquiv K L _ ) ⟨w.1, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨v, hv⟩, w⟩
    apply Sigma.subtype_ext
    · exact Subtype.ext ((primeBelowFiberEquiv K L v).symm w).2
    · rfl
  right_inv _ := rfl

/-- The total contribution of split fibers is the degree times the base prime sum. -/
theorem primeSum_split_fibers {s : ℝ} (hs : 1 < s) :
    ps {w : Prime L | primeBelow K L w ∈ Split K L} s =
      (Module.finrank K L : ℝ) * ps (Split K L) s := by
  let weight (w : Prime L) : ℝ := (norm w : ℝ) ^ (-s)
  have hw : Summable weight := _root_.Chebotarev.summable_primeNorm L s hs
  have hsum : Summable (fun x : Σ v : Split K L, v.1.asIdeal.primesOver (𝓞 L) ↦
      (x.2.1.absNorm : ℝ) ^ (-s)) :=
    (splitPrimeEquiv K L).summable_iff.mpr
      (hw.subtype (fun w ↦ primeBelow K L w ∈ Split K L))
  simp only [ps, NumberField.Set.primeIdealZetaSum_def]
  change (∑' w : {w : Prime L | primeBelow K L w ∈ Split K L}, weight w.1) = _
  calc
    _ = ∑' x : Σ v : Split K L, v.1.asIdeal.primesOver (𝓞 L),
        (x.2.1.absNorm : ℝ) ^ (-s) :=
      ((splitPrimeEquiv K L).tsum_eq (fun w ↦ weight w.1)).symm
    _ = ∑' v : Split K L, ∑' w : v.1.asIdeal.primesOver (𝓞 L),
        (w.1.absNorm : ℝ) ^ (-s) := hsum.tsum_sigma
    _ = ∑' v : Split K L, (Module.finrank K L : ℝ) *
        (norm v.1 : ℝ) ^ (-s) := by
      apply tsum_congr
      intro v
      simpa only [tsum_fintype, norm] using sum_norm_powers_over_split K L v.1 v.2.1 v.2.2 s
    _ = _ := ((_root_.Chebotarev.summable_primeNorm K s hs).subtype _).tsum_mul_left _

/-- Outside split fibers, each prime is over a ramified prime or has higher residue degree. -/
theorem nonsplit_subset_ramified_union_higherDegree :
    {w : Prime L | primeBelow K L w ∉ Split K L} ⊆
      {w : Prime L | ¬ Unram K L (primeBelow K L w)} ∪ HigherDegree K L := by
  intro w hw
  by_cases hu : Unram K L (primeBelow K L w)
  · right
    refine ⟨primeBelow K L w, rfl, ?_⟩
    have hf : frob K L (primeBelow K L w) ≠ 1 := fun h ↦ hw ⟨hu, h⟩
    let : w.asIdeal.LiesOver (primeBelow K L w).asIdeal := ⟨rfl⟩
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (primeBelow K L w).asIdeal w.asIdeal Gal(L/K)]
    exact two_le_inertiaDegIn_of_frob_ne_one K L _ hu hf
  · exact Or.inl hu

/-- Removing the split-fiber contribution leaves a bounded function near one. -/
theorem primeSum_sub_splitPrimeSum_bounded :
    Asymptotics.IsBigO (𝓝[>] (1 : ℝ))
      (fun s ↦ ps (Set.univ : Set (Prime L)) s -
        (Module.finrank K L : ℝ) * ps (Split K L) s) (fun _ ↦ (1 : ℝ)) := by
  classical
  let T : Set (Prime L) := {w | primeBelow K L w ∈ Split K L}
  let R : Set (Prime L) := {w | ¬ Unram K L (primeBelow K L w)}
  let H := HigherDegree K L
  have hbound := (primeSum_isBigO_of_finite (finite_ramified_fibers K L)).add
    (higherDegree_primeSum_bounded K L)
  have hle {s : ℝ} (hs : 1 < s) : ps Tᶜ s ≤ ps R s + ps H s := by
    let f (w : Prime L) : ℝ := (norm w : ℝ) ^ (-s)
    have hf : Summable f := _root_.Chebotarev.summable_primeNorm L s hs
    simp only [ps, NumberField.Set.primeIdealZetaSum_def]
    change (∑' w : ↥(Tᶜ), f w.1) ≤ (∑' w : R, f w.1) + ∑' w : H, f w.1
    simp only [tsum_subtype]
    rw [← (hf.indicator R).tsum_add (hf.indicator H)]
    apply Summable.tsum_le_tsum _ (hf.indicator Tᶜ)
      ((hf.indicator R).add (hf.indicator H))
    intro w
    have hpos : 0 ≤ f w := Real.rpow_nonneg (Nat.cast_nonneg _) _
    by_cases ht : w ∈ Tᶜ
    · have hx := nonsplit_subset_ramified_union_higherDegree K L ht
      change w ∈ R ∪ H at hx
      rcases hx with hr | hh
      · by_cases hh : w ∈ H <;> simp [Set.indicator, ht, hr, hh, hpos]
      · by_cases hr : w ∈ R <;> simp [Set.indicator, ht, hr, hh, hpos]
    · by_cases hr : w ∈ R <;> by_cases hh : w ∈ H <;>
        simp [Set.indicator, ht, hr, hh, hpos, add_nonneg hpos hpos]
  have hrem : Asymptotics.IsBigO (𝓝[>] (1 : ℝ)) (ps Tᶜ) (fun _ ↦ (1 : ℝ)) := by
    obtain ⟨c, hc⟩ := hbound.bound
    refine Asymptotics.IsBigO.of_bound c ?_
    filter_upwards [hc, self_mem_nhdsWithin] with s hs h1
    have hpR := NumberField.Set.primeIdealZetaSum_nonneg R s
    have hpH := NumberField.Set.primeIdealZetaSum_nonneg H s
    rw [Real.norm_eq_abs, abs_of_nonneg
      (NumberField.Set.primeIdealZetaSum_nonneg Tᶜ s), norm_one, mul_one]
    have hb : ps R s + ps H s ≤ c := by
      change ‖ps R s + ps H s‖ ≤ c * ‖(1 : ℝ)‖ at hs
      simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hpR hpH),
        abs_one, mul_one] using hs
    exact (hle h1).trans hb
  apply hrem.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsplit := primeSum_split_fibers K L hs
  have hsum := (_root_.Chebotarev.summable_primeNorm L s hs).tsum_subtype_add_tsum_subtype_compl T
  have hall : ps (Set.univ : Set (Prime L)) s =
      ∑' w : Prime L, (norm w : ℝ) ^ (-s) := by
    simp only [ps, NumberField.Set.primeIdealZetaSum_def]
    exact tsum_univ (fun w : Prime L ↦ (norm w : ℝ) ^ (-s))
  rw [hall, ← hsplit]
  change ps Tᶜ s = _ - ps T s
  apply eq_sub_iff_add_eq.mpr
  simp only [ps, NumberField.Set.primeIdealZetaSum_def]
  exact (add_comm _ _).trans hsum

end GaloisRepresentation.Chebotarev
