/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.NegligibleSets
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.PrimeSummability
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Higher residue degrees have bounded prime sums

Leaf D1 of `docs/CHEBOTAREV_PLAN.md`, for arbitrary extensions of number fields.
We use the norm identity and the ramification–inertia sum to dominate the sum
by a constant times the convergent square-reciprocal prime sum of the base field.
-/

@[expose] public section

noncomputable section

open Filter IsDedekindDomain NumberField
open scoped Topology

namespace GaloisRepresentation.Chebotarev

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- Prime ideals whose residue degree over the base field is at least two. -/
def HigherDegree : Set (Prime L) :=
  {w | ∃ v : Prime K, w.asIdeal.under (𝓞 K) = v.asIdeal ∧
    2 ≤ w.asIdeal.inertiaDeg (𝓞 K)}

/-- The number of primes above a base prime is bounded uniformly by the module rank. -/
theorem card_primesOver_le (v : Prime K) [Fintype (v.asIdeal.primesOver (𝓞 L))] :
    Fintype.card (v.asIdeal.primesOver (𝓞 L)) ≤ Module.finrank (𝓞 K) (𝓞 L) := by
  classical
  rw [← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L),
    Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun w _ ↦ Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_pos (Ideal.ramificationIdx_pos w.1 (𝓞 K))
      (Ideal.inertiaDeg_pos w.1 (𝓞 K))).ne'

/-- Above a prime with residue degree at least two, each norm power for `s > 1`
is bounded by the square reciprocal of the base norm. -/
theorem norm_rpow_le_of_inertiaDeg_ge_two (v : Prime K) (w : Prime L)
    (hw : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hf : 2 ≤ w.asIdeal.inertiaDeg (𝓞 K)) {s : ℝ} (hs : 1 < s) :
    (norm w : ℝ) ^ (-s) ≤ (norm v : ℝ) ^ (-(2 : ℝ)) := by
  let : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  have hn : 1 ≤ (norm v : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have heq := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  change (w.asIdeal.absNorm : ℝ) ^ (-s) ≤ (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ))
  rw [← heq, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  apply Real.rpow_le_rpow_of_exponent_le hn
  have hf' : (2 : ℝ) ≤ w.asIdeal.inertiaDeg (𝓞 K) := by exact_mod_cast hf
  nlinarith

/-- An explicit uniform bound for the higher-degree prime sum. -/
theorem higherDegree_primeSum_le {s : ℝ} (hs : 1 < s) :
    ps (HigherDegree K L) s ≤
      (Module.finrank (𝓞 K) (𝓞 L) : ℝ) *
        ∑' v : Prime K, (norm v : ℝ) ^ (-(2 : ℝ)) := by
  classical
  let (v : Prime K) : Fintype (v.asIdeal.primesOver (𝓞 L)) :=
    (Algebra.QuasiFinite.finite_primesOver v.asIdeal).fintype
  let weight (v : Prime K) : ℝ := (norm v : ℝ) ^ (-(2 : ℝ))
  let fiberWeight (x : Σ v : Prime K, v.asIdeal.primesOver (𝓞 L)) : ℝ := weight x.1
  have hweight : Summable weight := _root_.Chebotarev.summable_primeNorm K 2 (by norm_num)
  have hbound (v : Prime K) :
      (∑' w : v.asIdeal.primesOver (𝓞 L), fiberWeight ⟨v, w⟩) ≤
        (Module.finrank (𝓞 K) (𝓞 L) : ℝ) * weight v := by
    simp only [fiberWeight, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_primesOver_le K L v)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have houter : Summable (fun v : Prime K ↦
      ∑' w : v.asIdeal.primesOver (𝓞 L), fiberWeight ⟨v, w⟩) :=
    Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ by
      dsimp [fiberWeight, weight]; positivity) hbound (hweight.mul_left _)
  have hfiber : Summable fiberWeight :=
    (summable_sigma_of_nonneg (fun x ↦ by dsimp [fiberWeight, weight]; positivity)).mpr
      ⟨fun _ ↦ (hasSum_fintype _).summable, houter⟩
  let base (w : HigherDegree K L) : Prime K := w.2.choose
  have hbase (w : HigherDegree K L) :
      w.1.asIdeal.under (𝓞 K) = (base w).asIdeal ∧
        2 ≤ w.1.asIdeal.inertiaDeg (𝓞 K) := w.2.choose_spec
  let embed (w : HigherDegree K L) : Σ v : Prime K, v.asIdeal.primesOver (𝓞 L) :=
    ⟨base w, ⟨w.1.asIdeal, w.1.isPrime, ⟨(hbase w).1.symm⟩⟩⟩
  have hinj : Function.Injective embed := by
    intro w w' h
    apply Subtype.ext
    apply HeightOneSpectrum.asIdeal_injective
    exact congrArg (fun x : Σ v : Prime K, v.asIdeal.primesOver (𝓞 L) ↦ x.2.1) h
  calc
    ps (HigherDegree K L) s ≤ ∑' x, fiberWeight x := by
      dsimp only [ps]
      rw [NumberField.Set.primeIdealZetaSum_def]
      exact Summable.tsum_le_tsum_of_inj embed hinj
        (fun x _ ↦ by dsimp [fiberWeight, weight]; positivity)
        (fun w ↦ norm_rpow_le_of_inertiaDeg_ge_two K L
          (base w) w.1 (hbase w).1 (hbase w).2 hs)
        ((_root_.Chebotarev.summable_primeNorm L s hs).subtype _) hfiber
    _ = ∑' v : Prime K, ∑' w : v.asIdeal.primesOver (𝓞 L), fiberWeight ⟨v, w⟩ :=
      hfiber.tsum_sigma
    _ ≤ ∑' v : Prime K, (Module.finrank (𝓞 K) (𝓞 L) : ℝ) * weight v :=
      Summable.tsum_le_tsum hbound houter (hweight.mul_left _)
    _ = _ := hweight.tsum_mul_left _

/-- Higher residue degrees contribute a bounded prime sum as `s` tends to one
from above. No Galois hypothesis is required. -/
theorem higherDegree_primeSum_bounded :
    Asymptotics.IsBigO (𝓝[>] (1 : ℝ))
      (ps (HigherDegree K L)) (fun _ ↦ (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound
    ((Module.finrank (𝓞 K) (𝓞 L) : ℝ) *
      ∑' v : Prime K, (norm v : ℝ) ^ (-(2 : ℝ))) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (NumberField.Set.primeIdealZetaSum_nonneg (HigherDegree K L) s), norm_one, mul_one]
    using higherDegree_primeSum_le K L hs

end GaloisRepresentation.Chebotarev
