/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PadicOrderTopology

/-!
# The constructed general-prime normalization topology

The spectral norm is selected here, so the endpoint assumes no norm or
completeness on the original fraction field. The original embedding is retained.
-/

@[expose] public noncomputable section
namespace PadicOrderPlan

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra ℤ_[p] R]
  [IsDomain R] [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]
  [TopologicalSpace R] [IsModuleTopology ℤ_[p] R]

/-- The constructed norm supplies completeness, module topologies and continuous embeddings. -/
theorem canonical_normalization_topology :
    let := fractionNormedField p R
    let := fractionNormedAlgebra p R
    CompactSpace (NormalizedOrder p R) ∧ CompleteSpace (FractionRing R) ∧
      CompleteSpace (NormalizedOrder p R) ∧ IsModuleTopology ℤ_[p] (NormalizedOrder p R) ∧
      IsModuleTopology ℚ_[p] (FractionRing R) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (NormalizedOrder p R)) (NormalizedOrder p R) ∧
      Continuous (toNormalizedOrder p R) ∧
      Continuous (algebraMap ℚ_[p] (FractionRing R)) ∧
      ContinuousSMul R (NormalizedOrder p R) ∧ ContinuousSMul R (FractionRing R) := by
  let := fractionNormedField p R
  let := fractionNormedAlgebra p R
  exact ⟨inferInstance, fraction_completeSpace p R, normalizedOrder_completeSpace p R,
    normalizedOrder_isModuleTopology p R, fraction_isModuleTopology p R,
    normalizedOrder_isAdicComplete p R, continuous_toNormalizedOrder p R,
    continuous_algebraMap ℚ_[p] (FractionRing R), inferInstance, fractionOrderContinuousSMul p R⟩

end PadicOrderPlan
