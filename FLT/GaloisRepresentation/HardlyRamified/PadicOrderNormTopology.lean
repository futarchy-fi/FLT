/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PadicOrderValuation

/-!
# The spectral norm topology on the general-prime normalized order

The integral order's type retains p, so its norm is unambiguous. The norm
on its original fraction field is selected explicitly in field statements.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PadicOrderPlan

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra ℤ_[p] R]
  [IsDomain R] [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]

/-- The normalization inherits the constructed spectral norm. -/
scoped instance normalizedOrderNormedCommRing : NormedCommRing (NormalizedOrder p R) := by
  letI := fractionNormedField p R
  exact inferInstanceAs (NormedCommRing (integralClosure ℤ_[p] (FractionRing R)))

/-- Prefer the constructed integral topology over unrelated localization topologies. -/
scoped instance (priority := 1100) normalizedOrderTopology :
    TopologicalSpace (NormalizedOrder p R) :=
  (normalizedOrderNormedCommRing p R).toUniformSpace.toTopologicalSpace

/-- The p-adic integers act continuously on the chosen fraction-field topology. -/
theorem fractionContinuousSMul :
    letI := fractionNormedField p R
    ContinuousSMul ℤ_[p] (FractionRing R) := by
  let := fractionNormedField p R
  let := fractionNormedAlgebra p R
  apply continuousSMul_of_algebraMap
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (FractionRing R)]
  exact (continuous_algebraMap ℚ_[p] (FractionRing R)).comp continuous_subtype_val

/-- The integral scalar action is continuous for the constructed topology. -/
scoped instance normalizedOrderPadicContinuousSMul :
    ContinuousSMul ℤ_[p] (NormalizedOrder p R) := by
  let := fractionNormedField p R
  let := fractionContinuousSMul p R
  exact inferInstanceAs (ContinuousSMul ℤ_[p] (integralClosure ℤ_[p] (FractionRing R)))

/-- The chosen fraction field is complete. -/
theorem fraction_completeSpace :
    letI := fractionNormedField p R
    CompleteSpace (FractionRing R) := by
  let := fractionNormedField p R
  let := fractionNormedAlgebra p R
  exact FiniteDimensional.complete ℚ_[p] (FractionRing R)

/-- The chosen fraction-field topology is its finite-dimensional module topology. -/
theorem fraction_isModuleTopology :
    letI := fractionNormedField p R
    IsModuleTopology ℚ_[p] (FractionRing R) := by
  let := fractionNormedField p R
  let := fractionNormedAlgebra p R
  exact isModuleTopologyOfFiniteDimensional

end PadicOrderPlan
