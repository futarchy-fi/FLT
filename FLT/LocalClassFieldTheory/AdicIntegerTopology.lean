/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DvrAdicTopology
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# The induced topology on a DVR

Pulling back the actual fraction-field uniformity gives the maximal-ideal
adic topology on the integer ring. Algebraic adic completeness therefore
makes its image in the fraction field a complete subset.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Filter IsLocalRing IsDedekindDomain
open scoped Topology WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The fraction-field uniformity pulled back to its ring of integers. -/
@[instance_reducible] def dvrIntegerUniformity : UniformSpace S :=
  letI := dvrAdicValued S L
  UniformSpace.comap (algebraMap S L) inferInstance

/-- The induced uniformity on the DVR is its maximal-ideal adic topology. -/
theorem dvrIntegerUniformity_isAdic :
    letI := dvrIntegerUniformity S L
    IsAdic (maximalIdeal S) := by
  let := dvrAdicValued S L
  let := dvrIntegerUniformity S L
  have hi : IsUniformInducing (algebraMap S L) := ⟨rfl⟩
  let : IsUniformAddGroup S := IsUniformAddGroup.comap (algebraMap S L)
  let : ContinuousMul S := continuousMul_induced (algebraMap S L)
  let : IsTopologicalRing S :=
    { continuous_add := continuous_add
      continuous_mul := continuous_mul
      continuous_neg := continuous_neg }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hπv : (dvrPrime S).valuation L (algebraMap S L π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq
  have hpow (n : ℕ) :
      Valued.v (algebraMap S L π ^ n) = WithZero.exp (-(n : ℤ)) := by
    change (dvrPrime S).valuation L _ = _
    rw [map_pow, hπv, ← WithZero.exp_nsmul]
    simp
  have hmem (x : S) (n : ℕ) : x ∈ maximalIdeal S ^ n ↔
      Valued.v.restrict (algebraMap S L x) ≤
        Valued.v.restrict (algebraMap S L π ^ n) := by
    rw [Valuation.restrict_le_iff, hpow]
    change x ∈ (dvrPrime S).asIdeal ^ n ↔
      (dvrPrime S).valuation L (algebraMap S L x) ≤ _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact ((dvrPrime S).intValuation_le_pow_iff_mem x n).symm
  apply isAdic_iff.mpr
  constructor
  · intro n
    have hn : Valued.v.restrict (algebraMap S L π ^ n) ≠ 0 := by
      exact (map_ne_zero _).mpr (pow_ne_zero _
        (by simpa using (IsFractionRing.injective S L).ne hπ.ne_zero))
    convert (Valued.isOpen_closedBall (R := L) hn).preimage hi.uniformContinuous.continuous using 1
    ext x
    exact hmem x n
  · intro U hU
    rw [hi.isInducing.nhds_eq_comap, map_zero] at hU
    obtain ⟨V, hV, hVU⟩ := mem_comap.mp hU
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
    have ht : Tendsto (fun n : ℕ => algebraMap S L π ^ n) atTop (𝓝 0) :=
      Valued.tendsto_zero_pow_of_v_lt_one (by
        change (dvrPrime S).valuation L _ < 1
        rw [hπv]; exact WithZero.exp_lt_exp.mpr (by omega))
    have hb : {x : L | Valued.v.restrict x < γ.val} ∈ 𝓝 (0 : L) :=
      Valued.mem_nhds_zero.mpr ⟨γ, Set.Subset.rfl⟩
    obtain ⟨n, hn⟩ := (ht.eventually hb).exists
    exact ⟨n, fun x hx => hVU (hγ ((hmem x n).mp hx |>.trans_lt hn))⟩

end LocalClassFieldTheory
