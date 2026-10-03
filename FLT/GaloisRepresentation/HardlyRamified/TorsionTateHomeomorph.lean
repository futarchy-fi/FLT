/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionTateFree
public import FLT.GroupScheme.PDivisibleTateCompact
public import Mathlib.Topology.Algebra.Module.Compact

/-! # Topological recovery of the original p-adic lattice -/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified
variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  [Module ℤ_[p] V] [IsScalarTower ℤ_[p] R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

variable [TopologicalSpace V] [IsModuleTopology ℤ_[p] V]

/-- The actual recovery map is continuous for the original module topology. -/
theorem continuous_torsionTateRecovery : Continuous hρ.torsionTateRecovery :=
  IsModuleTopology.continuous_of_linearMap hρ.torsionTateRecoveryLinear.toLinearMap

/-- Recovery is a homeomorphism, with the original lattice topology. -/
def torsionTateHomeomorph : V ≃ₜ hρ.torsionPDivisibleUniverses.tateSequences := by
  letI : Module.Finite ℤ_[p] V := Module.Finite.trans R V
  letI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℤ_[p] V
  letI : CompactSpace V := Module.Finite.compactSpace (R := ℤ_[p]) V
  exact hρ.torsionTateRecovery.toEquiv.toHomeomorphOfContinuousClosed
    hρ.continuous_torsionTateRecovery hρ.continuous_torsionTateRecovery.isClosedMap

/-- The recovered equivalence is simultaneously linear and a homeomorphism. -/
def torsionTateContinuousLinearEquiv : V ≃L[ℤ_[p]] hρ.torsionPDivisibleUniverses.tateSequences where
  __ := hρ.torsionTateRecoveryLinear
  continuous_toFun := hρ.torsionTateHomeomorph.continuous_toFun
  continuous_invFun := hρ.torsionTateHomeomorph.continuous_invFun

/-- The product-limit topology is the finite p-adic module topology. -/
theorem torsionTate_isModuleTopology :
    IsModuleTopology ℤ_[p] hρ.torsionPDivisibleUniverses.tateSequences :=
  IsModuleTopology.iso hρ.torsionTateContinuousLinearEquiv

end GaloisRepresentation.IsHardlyRamified
