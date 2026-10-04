/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TameInertiaCyclic

/-!
# The inertia character of a nonzero integer

An integer of valuation k transforms modulo units with residue equal to the
k-th power of the uniformizer character. The exponent is its actual valuation.
-/

@[expose] public noncomputable section
open IsLocalRing IsDiscreteValuationRing
namespace ThreeAdicPlan
variable {R G : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Group G] [MulSemiringAction G R] {π : R} (hπ : Irreducible π)

/-- Inertia ratios of any nonzero integer reduce to the valuation power of the tame character. -/
theorem exists_uniformizer_power_ratio {x : R} (hx : x ≠ 0) :
    ∃ k : ℕ, addVal R x = k ∧ ∀ g : (IsLocalRing.maximalIdeal R).inertia G,
      ∃ z : R, g.val • x = z * x ∧
        residue R z = (uniformizerCharacter hπ g : ResidueField R) ^ k := by
  obtain ⟨k, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ
  refine ⟨k, ?_, fun g ↦ ?_⟩
  · rw [hu, addVal_def' u hπ k]
  · let z := (g.val • (u : R)) * (u⁻¹ : Rˣ) * (uniformizerRatio hπ g.val : R) ^ k
    refine ⟨z, ?_, ?_⟩
    · rw [hu, smul_mul', smul_pow', ← uniformizer_mul_ratio hπ g.val, mul_pow]
      have hi : ((u⁻¹ : Rˣ) : R) * u = 1 := Units.inv_mul u
      dsimp only [z]
      calc
        (g.val • (u : R)) * (π ^ k * (uniformizerRatio hπ g.val : R) ^ k) =
            (g.val • (u : R)) * (π ^ k * (uniformizerRatio hπ g.val : R) ^ k) *
              (((u⁻¹ : Rˣ) : R) * u) := by rw [hi, mul_one]
        _ = _ := by ring
    · change residue R z = residue R (uniformizerRatio hπ g.val : R) ^ k
      dsimp only [z]
      rw [map_mul, map_mul, map_pow, residue_inertia_smul, ← map_mul,
        Units.mul_inv, map_one, one_mul]

end ThreeAdicPlan
