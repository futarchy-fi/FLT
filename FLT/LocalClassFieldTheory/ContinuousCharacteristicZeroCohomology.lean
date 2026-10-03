/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCohomologyColimit
public import FLT.LocalClassFieldTheory.FiniteCharacteristicZeroCohomology

/-!
# Positive continuous cohomology in characteristic zero

Every continuous class descends to a finite quotient with invariant
coefficients. Maschke's theorem kills that finite-stage class, hence the
original class. In particular this applies to discrete rational modules.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits HomologicalComplex

variable (k G M : Type u) [Field k] [CharZero k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- All positive continuous cohomology classes with characteristic-zero field
coefficients vanish, including nontrivial continuous actions. -/
theorem continuousCharacteristicZero_cohomology_eq_zero (n : ℕ)
    (x : continuousCohomology k G M (n + 1)) : x = 0 := by
  obtain ⟨N, y, rfl⟩ := complexCocone_homology_surjective
    (invariantStageDiagram k G M) (continuousStageCocone k G M)
    (continuousStageInflation_injective k G M)
    (continuousStageInflation_jointly_surjective k G M) (n + 1) x
  let P : OpenNormalSubgroup G := OrderDual.ofDual N
  let : Finite (G ⧸ P.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen P.toSubgroup P.isOpen
  have hzero : IsZero (((invariantStageDiagram k G M).obj N).homology (n + 1)) :=
    finiteCharacteristicZero_cohomology_isZero k (G ⧸ P.toSubgroup) _ n
  have hy : y = 0 := (ModuleCat.isZero_iff_subsingleton.mp hzero).elim y 0
  rw [hy, map_zero]
  rfl

/-- Positive continuous cohomology is the zero module over any characteristic-zero field. -/
theorem continuousCharacteristicZero_cohomology_isZero (n : ℕ) :
    IsZero (continuousCohomology k G M (n + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (continuousCharacteristicZero_cohomology_eq_zero k G M n x).trans
    (continuousCharacteristicZero_cohomology_eq_zero k G M n y).symm⟩

end LocalClassFieldTheory
