/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.Generators
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.SplittingDensity

/-!
# Density of generating Frobenius elements

Leaf W1 of `docs/CHEBOTAREV_PLAN.md`. Splitting in fixed fields gives the
density of subgroup membership after removing the finitely many primes
ramified in the top field. Inclusion-exclusion then gives the proportion
of generators of the cyclic Galois group, including the trivial group.
-/

@[expose] public section

open Filter NumberField
open scoped Topology BigOperators

namespace GaloisRepresentation.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Unramified primes whose Frobenius generates the Galois group. -/
def Generators : Set (Prime K) :=
  {v | Unram K L v ∧ Subgroup.zpowers (frob K L v) = ⊤}

/-- Frobenius membership in a normal subgroup has density equal to its
proportion of the Galois group. -/
theorem logDensity_frob_mem (D : Subgroup Gal(L/K)) [D.Normal] :
    LogDensity {v : Prime K | Unram K L v ∧ frob K L v ∈ D}
      ((Nat.card D : ℝ) / Nat.card Gal(L/K)) := by
  have hset : {v : Prime K | Unram K L v ∧ frob K L v ∈ D} =
      Split K (IntermediateField.fixedField D) \ {v | ¬ Unram K L v} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_not]
    exact ⟨fun h ↦ ⟨(frob_mem_iff_split_fixedField_of_normal K L D v h.1).mp h.2, h.1⟩,
      fun h ↦ ⟨h.2, (frob_mem_iff_split_fixedField_of_normal K L D v h.2).mpr h.1⟩⟩
  have hdegree : (Module.finrank K (IntermediateField.fixedField D) : ℝ) *
      (Nat.card D : ℝ) = Nat.card Gal(L/K) := by
    rw [← Nat.cast_mul, ← IntermediateField.finrank_fixedField_eq_card,
      Module.finrank_mul_finrank, IsGalois.card_aut_eq_finrank]
  have hD : (Nat.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoeff : 1 / (Module.finrank K (IntermediateField.fixedField D) : ℝ) =
      (Nat.card D : ℝ) / Nat.card Gal(L/K) := by
    rw [← hdegree, div_mul_cancel_right₀ hD, one_div]
  rw [hset, ← hcoeff]
  exact logDensity_diff (_root_.Chebotarev.summable_primeNorm K) _ _ _
    (logDensity_split K (IntermediateField.fixedField D))
    (primeSum_isBigO_of_finite (finite_ramified K L))

open _root_.Chebotarev in
/-- Inclusion-exclusion for the prime sum of generating Frobenius elements. -/
theorem primeSum_generators (s : ℝ) (hs : 1 < s) :
    ps (Generators K L) s =
      ∑ J ∈ (Finset.univ : Finset (_root_.Chebotarev.Max Gal(L/K))).powerset,
        (-1 : ℝ) ^ J.card * ps {v : Prime K | Unram K L v ∧ frob K L v ∈ D Gal(L/K) J} s := by
  classical
  let f : Prime K → ℝ := fun v ↦ (norm v : ℝ) ^ (-s)
  let T (J : Finset (_root_.Chebotarev.Max Gal(L/K))) : Set (Prime K) :=
    {v | Unram K L v ∧ frob K L v ∈ D Gal(L/K) J}
  have hpoint (v : Prime K) : (Generators K L).indicator f v =
      ∑ J ∈ (Finset.univ : Finset (_root_.Chebotarev.Max Gal(L/K))).powerset,
        (-1 : ℝ) ^ J.card * (T J).indicator f v := by
    by_cases hu : Unram K L v
    · simpa [Set.indicator_apply, Generators, T, hu, Finset.sum_mul, mul_assoc,
        ite_mul] using congrArg (fun x : ℝ ↦ x * f v) (generator_indicator (frob K L v))
    · simp [Generators, T, hu]
  simp only [ps, NumberField.Set.primeIdealZetaSum_def]
  change (∑' v : Generators K L, f v) =
    ∑ J ∈ (Finset.univ : Finset (_root_.Chebotarev.Max Gal(L/K))).powerset,
      (-1 : ℝ) ^ J.card * ∑' v : T J, f v
  simp_rw [tsum_subtype]
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
  · intro J hJ
    exact ((_root_.Chebotarev.summable_primeNorm K s hs).indicator (T J)).mul_left _

open _root_.Chebotarev in
/-- In a cyclic Galois extension, generating Frobenius elements have logarithmic
density `φ(|Gal(L/K)|) / |Gal(L/K)|` (leaf W1). -/
theorem logDensity_generators [IsCyclic Gal(L/K)] :
    LogDensity (Generators K L)
      ((Nat.totient (Nat.card Gal(L/K)) : ℝ) / Nat.card Gal(L/K)) := by
  classical
  have hlim := tendsto_finsetSum (Finset.univ : Finset (_root_.Chebotarev.Max Gal(L/K))).powerset
    (fun J _ ↦ (logDensity_frob_mem K L (D Gal(L/K) J)).const_mul ((-1 : ℝ) ^ J.card))
  simp only [← mul_div_assoc] at hlim
  rw [generator_density_coefficient] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [← Finset.sum_div, primeSum_generators K L s hs]

end GaloisRepresentation.Chebotarev
