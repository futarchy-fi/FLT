/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateTopology
public import FLT.Deformations.RepresentationTheory.PadicIdealOpen
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-! # Compactness and continuous p-adic scalars on the Tate module -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Residue reduction of p-adic scalars is continuous. -/
theorem continuous_padicResidue (n : ℕ) : Continuous (PadicInt.toZModPow (p := p) n) := by
  let : UniformSpace (ZMod (p ^ n)) := ⊥
  let : IsUniformAddGroup (ZMod (p ^ n)) := inferInstance
  apply UniformContinuous.continuous
  rw [IsUniformAddGroup.uniformContinuous_iff_isOpen_ker]
  change IsOpen (RingHom.ker (PadicInt.toZModPow (p := p) n) : Set ℤ_[p])
  rw [PadicInt.ker_toZModPow]
  exact PadicInt.isOpen_span_p_pow p ℤ_[p] n

/-- Scalar multiplication is jointly continuous at each finite level. -/
instance instContinuousSMulPadicPoints (n : ℕ) : ContinuousSMul ℤ_[p] (X.level n).Points where
  continuous_smul := by
    change Continuous (fun x : ℤ_[p] × (X.level n).Points ↦
      PadicInt.toZModPow n x.1 • x.2)
    exact (continuous_of_discreteTopology (f := fun y : ZMod (p ^ n) ×
      (X.level n).Points ↦ y.1 • y.2)).comp
      (((continuous_padicResidue n).comp continuous_fst).prodMk continuous_snd)

/-- The canonical p-adic action on the Tate module is jointly continuous. -/
instance instContinuousSMulPadicTate : ContinuousSMul ℤ_[p] X.tateSequences where
  continuous_smul := (X.continuous_tate_iff _).mpr fun n ↦
    continuous_fst.smul ((X.continuous_tateEval n).comp continuous_snd)

/-- Coherence is a closed condition in the product of finite discrete groups. -/
theorem isClosed_tateSequences : IsClosed (X.tateSequences : Set (∀ n, (X.level n).Points)) := by
  change IsClosed {x : ∀ n, (X.level n).Points |
    ∀ m n (h : m ≤ n), genericHom (X.reduction h) (x n) = x m}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n)) (continuous_apply m)

/-- The Tate module is compact as a closed subspace of a product of finite groups. -/
instance instCompactSpaceTate : CompactSpace X.tateSequences :=
  isCompact_iff_compactSpace.mp X.isClosed_tateSequences.isCompact

end ThreeAdicPlan.PDivisibleSystem
