/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.WittCoefficientResidue
public import FLT.Deformations.HardlyRamifiedFlatLift
public import FLT.GaloisRepresentation.HardlyRamified.CoefficientQuotient

/-!
# The original residual representation over the Witt coefficient base

Transport the given finite coefficient field through the constructed residue
isomorphism. The residual representation retains all hardly-ramified conditions,
so the effective flat deformation quotient can be formed over W(k).
-/

@[expose] public noncomputable section
open scoped TensorProduct Deformation.WittCoefficients
open GaloisRepresentation
namespace Deformation.WittCoefficients
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Finite k]
  [Algebra ℤ_[p] k] [TopologicalSpace k] [IsTopologicalRing k] [DiscreteTopology k]
local notation "κ" => ProartinianCat.residueField (𝓞 := WittVector p k)

/-- The category residue object carries the canonical p-adic scalar action. -/
scoped instance residualPadicAlgebra : Algebra ℤ_[p] κ :=
  inferInstanceAs (Algebra ℤ_[p] (IsLocalRing.ResidueField (WittVector p k)))

/-- Its p-adic action factors through the Witt coefficient ring. -/
scoped instance residualPadicTower : IsScalarTower ℤ_[p] (WittVector p k) κ :=
  inferInstanceAs (IsScalarTower ℤ_[p] (WittVector p k)
    (IsLocalRing.ResidueField (WittVector p k)))

/-- The original field acts on the actual residue field through the constructed inverse. -/
scoped instance originalResidueAlgebra : Algebra k κ :=
  (residueEquiv p k).symm.toRingHom.toAlgebra

/-- This transport preserves the given integral p-adic scalars. -/
scoped instance originalResidueTower : IsScalarTower ℤ_[p] k κ :=
  IsScalarTower.of_algebraMap_eq' (residueAlgEquiv p k).symm.toAlgHom.comp_algebraMap.symm

/-- Residual coefficient transport is continuous for the discrete residue topologies. -/
scoped instance originalResidueContinuousSMul : ContinuousSMul k κ :=
  ⟨continuous_of_discreteTopology⟩

variable {V : Type} [AddCommGroup V] [Module k V]
  [Module.Finite k V] [Module.Free k V]
  (hdim : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)

omit [Algebra ℤ_[p] k] [TopologicalSpace k] [IsTopologicalRing k]
  [DiscreteTopology k] [Module.Finite k V] in
include hdim in
/-- Dimension two is retained by the constructed residual coefficient change. -/
theorem residual_rank : Module.rank κ (κ ⊗[k] V) = 2 := by
  simpa only [Module.rank_baseChange, Cardinal.lift_id] using hdim

/-- The original representation on the actual residue field of W(k). -/
def residualRep : GaloisRep ℚ κ (κ ⊗[k] V) := ρ.baseChange κ

variable (hp : Odd p) (hρ : IsHardlyRamified hp hdim ρ)

include hρ in
/-- No new local-condition hypothesis is required after this residue transport. -/
theorem residual_hardlyRamified :
    IsHardlyRamified hp (residual_rank p k hdim) (residualRep p k ρ) := by
  apply B5Inputs.hardlyRamified_of_surjective_coefficients hp
    (R := k) (A := κ) (residueEquiv p k).symm.surjective hdim
    (residual_rank p k hdim) hρ

/-- The actual simultaneous arithmetic and finite-flat quotient over the Witt base. -/
def flatObject : ProartinianCat (WittVector p k) :=
  hardlyFlatObject (WittVector p k) hp (residual_rank p k hdim) (residualRep p k ρ)
    (residual_hardlyRamified p k hdim ρ hp hρ)

/-- Its universal lift has the transported original residual representation. -/
def flatLift : ContinuousFramedLifts (WittVector p k) (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual (WittVector p k) hp (residual_rank p k hdim)
      (residualRep p k ρ) (residual_hardlyRamified p k hdim ρ hp hρ))
    (flatObject p k hdim ρ hp hρ) :=
  hardlyFlatLift (WittVector p k) hp (residual_rank p k hdim) (residualRep p k ρ)
    (residual_hardlyRamified p k hdim ρ hp hρ)

end Deformation.WittCoefficients
