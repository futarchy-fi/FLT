/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.TameRootsOfUnity
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Adic completeness at every finite number-field place

The actual valuation topology on the completion integers is the maximal-ideal
adic topology. Closedness in the complete local field supplies completeness,
and hence Henselianity, without a rational-place restriction.
-/

@[expose] public noncomputable section
open NumberField IsLocalRing Filter
open scoped Topology WithZero
namespace LocalRoot
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

/-- The given topology on the local integers is the maximal-ideal adic topology. -/
theorem completionIntegers_isAdic : IsAdic (maximalIdeal O) := by
  obtain ⟨π, hπ⟩ :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer K v
  change Valued.v π.1 = WithZero.exp (-1 : ℤ) at hπ
  have hpow (n : ℕ) : Valued.v (π.1 ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    simp
  have hmem (x : O) (n : ℕ) : x ∈ maximalIdeal O ^ n ↔
      Valued.v.restrict x.1 ≤ Valued.v.restrict (π.1 ^ n) := by
    rw [Valuation.restrict_le_iff, hpow]
    exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow K v x
  apply isAdic_iff.mpr
  constructor
  · intro n
    have hn : Valued.v.restrict (π.1 ^ n) ≠ 0 := by
      apply (map_ne_zero _).mpr
      apply pow_ne_zero
      intro h
      have hz := hpow 1
      rw [h, zero_pow (by omega), map_zero] at hz
      exact WithZero.exp_ne_zero hz.symm
    convert (Valued.isOpen_closedBall (R := F) hn).preimage continuous_subtype_val using 1
    ext x
    exact hmem x n
  · intro U hU
    rw [nhds_subtype_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := mem_comap.mp hU
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
    have ht : Tendsto (fun n : ℕ ↦ π.1 ^ n) atTop (𝓝 (0 : F)) :=
      Valued.tendsto_zero_pow_of_v_lt_one (by
        rw [hπ]
        exact WithZero.exp_lt_exp.mpr (by omega))
    have hb : {x : F | Valued.v.restrict x < γ.val} ∈ 𝓝 (0 : F) :=
      Valued.mem_nhds_zero.mpr ⟨γ, Set.Subset.rfl⟩
    obtain ⟨n, hn⟩ := (ht.eventually hb).exists
    exact ⟨n, fun x hx ↦ hVU (hγ ((hmem x n).mp hx |>.trans_lt hn))⟩

/-- The actual completion integers are algebraically complete at their maximal ideal. -/
theorem completionIntegers_adicComplete : IsAdicComplete (maximalIdeal O) O := by
  let : CompleteSpace O := (Valued.isClosed_valuationSubring F).completeSpace_coe
  exact (completionIntegers_isAdic v).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

/-- Every finite number-field completion has Henselian integers. -/
theorem completionIntegers_henselian : HenselianLocalRing O := by
  let := completionIntegers_adicComplete v
  exact henselian_of_adicComplete O

/-- All tame roots of unity already lie in the actual local base field. -/
theorem completion_exists_primitive_tame_root :
    ∃ z : F, IsPrimitiveRoot z (Nat.card (ResidueField O) - 1) := by
  let := completionIntegers_henselian v
  obtain ⟨z, hz⟩ := exists_primitive_tame_root (R := O)
  exact ⟨z.1, hz.map_of_injective (f := algebraMap O F) (IsFractionRing.injective O F)⟩

end LocalRoot
