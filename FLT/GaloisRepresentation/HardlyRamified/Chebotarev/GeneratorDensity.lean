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

end GaloisRepresentation.Chebotarev
