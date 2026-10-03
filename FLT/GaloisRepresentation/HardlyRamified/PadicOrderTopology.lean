/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PadicOrderNormTopology

/-!
# General-prime order normalization: Topology

The construction retains the original order and its fraction field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PadicOrderPlan
open scoped nonZeroDivisors

variable (p : ℕ) [Fact p.Prime]
variable (R : Type*) [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
  [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]

/-- The original order acts on its normalization through the canonical embedding. -/
scoped instance normalizedOrderAlgebra : Algebra R (NormalizedOrder p R) :=
  (toNormalizedOrder p R).toRingHom.toAlgebra

scoped instance normalizedOrderScalarTower : IsScalarTower ℤ_[p] R (NormalizedOrder p R) :=
  .of_algebraMap_eq fun x ↦ ((toNormalizedOrder p R).commutes x).symm

scoped instance normalizedOrderFractionScalarTower :
    IsScalarTower R (NormalizedOrder p R) (FractionRing R) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The normalization is compact in the topology inherited from its fraction field. -/
scoped instance normalizedOrderCompactSpace : CompactSpace (NormalizedOrder p R) :=
  Module.Finite.compactSpace ℤ_[p] (NormalizedOrder p R)

/-- The normalization is complete in its induced uniform structure. -/
theorem normalizedOrder_completeSpace : CompleteSpace (NormalizedOrder p R) :=
  complete_of_compact

/-- The induced topology on the normalization is its finite module topology. -/
theorem normalizedOrder_isModuleTopology : IsModuleTopology ℤ_[p] (NormalizedOrder p R) := by
  let b := Module.Free.chooseBasis ℤ_[p] (NormalizedOrder p R)
  let e := b.equivFun.symm
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  exact IsModuleTopology.of_isQuotientMap _ e.toLinearMap
    (hc.isClosedMap.isQuotientMap hc e.surjective)

open scoped Pointwise in
/-- The normalization is complete for powers of its maximal ideal. -/
theorem normalizedOrder_isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (NormalizedOrder p R)) (NormalizedOrder p R) where
  prec' f hf := by
    let m := IsLocalRing.maximalIdeal (NormalizedOrder p R)
    let S n : Set (NormalizedOrder p R) := f n +ᵥ ((m ^ n : Ideal (NormalizedOrder p R)) : Set _)
    have hS n : S (n + 1) ⊆ S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (m ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hS (by simp [S]) h
    refine ⟨L, fun n ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

attribute [scoped instance] normalizedOrder_completeSpace
  normalizedOrder_isModuleTopology normalizedOrder_isAdicComplete

variable [TopologicalSpace R] [IsModuleTopology ℤ_[p] R]

/-- The normalization map is continuous for the coefficient ring's module topology. -/
theorem continuous_toNormalizedOrder : Continuous (toNormalizedOrder p R) :=
  IsModuleTopology.continuous_of_linearMap (toNormalizedOrder p R).toLinearMap

/-- The original coefficient ring acts continuously on its normalization. -/
scoped instance normalizedOrderContinuousSMul : ContinuousSMul R (NormalizedOrder p R) :=
  continuousSMul_of_algebraMap _ _ (continuous_toNormalizedOrder p R)

/-- The original coefficient ring acts continuously on the fraction field. -/
theorem fractionOrderContinuousSMul :
    letI := fractionNormedField p R
    ContinuousSMul R (FractionRing R) := by
  let := fractionNormedField p R
  apply continuousSMul_of_algebraMap
  rw [IsScalarTower.algebraMap_eq R (NormalizedOrder p R) (FractionRing R)]
  exact continuous_subtype_val.comp (continuous_toNormalizedOrder p R)

end PadicOrderPlan
