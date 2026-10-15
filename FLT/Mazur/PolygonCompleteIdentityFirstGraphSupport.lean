/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphConductor
public import FLT.Mazur.PolygonSmoothingCoordinateIdeal

/-!
# The original first-order graph conductor is supported at the node

Construct the actual conductor ideal in the original node ring. It contains
positive powers of both original coordinates, so its closed vanishing locus
is contained in the original node locus. This retains the possibly nonzero
infinitesimal discrepancy rather than replacing its conductor by a radical.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "C" => firstNodeBranchSubalgebra (R)
local notation "β" => firstNodeBranchPair (R)
local notation "G" => completeIdentityFirstGraphAlgebra K n h i

/-- The exact conductor of the original node inside its original action graph. -/
def completeIdentityFirstGraphConductorIdeal : Ideal (B) where
  carrier := {w | ∀ z ∈ (G), z * (β) w ∈ (C)}
  zero_mem' := by intro z _; simp only [map_zero, mul_zero]; exact (C).zero_mem
  add_mem' := by
    intro a b ha hb z hz
    rw [map_add, mul_add]
    exact (C).add_mem (ha z hz) (hb z hz)
  smul_mem' := by
    intro a b hb z hz
    change z * (β) (a * b) ∈ (C)
    rw [map_mul, mul_left_comm]
    exact (C).mul_mem ⟨a, rfl⟩ (hb z hz)

/-- The original parameter belongs to the full conductor ideal before taking radicals. -/
theorem completeIdentityFirstGraphConductorIdeal_parameter :
    algebraMap (S) (B) (e) ∈ completeIdentityFirstGraphConductorIdeal K n h i := by
  intro z hz
  rw [AlgHom.commutes, mul_comm, ← Algebra.smul_def]
  exact completeIdentityFirstGraphAlgebra_parameter K n h i z hz

/-- A positive power of the original left coordinate belongs to the actual conductor ideal. -/
theorem completeIdentityFirstGraphConductorIdeal_left :
    ∃ m : ℕ, 0 < m ∧ leftCoordinate (e) ^ m ∈
      completeIdentityFirstGraphConductorIdeal K n h i :=
  completeIdentityFirstGraphAlgebra_left_conductor K n h i

/-- The original right coordinate likewise has a positive power in the conductor. -/
theorem completeIdentityFirstGraphConductorIdeal_right :
    ∃ m : ℕ, 0 < m ∧ rightCoordinate (e) ^ m ∈
      completeIdentityFirstGraphConductorIdeal K n h i :=
  completeIdentityFirstGraphAlgebra_right_conductor K n h i

/-- Both original node equations lie in the radical of the actual conductor ideal. -/
theorem completeIdentityFirstGraphConductorIdeal_node :
    coordinateIdeal (e) ≤ (completeIdentityFirstGraphConductorIdeal K n h i).radical := by
  rw [coordinateIdeal, Ideal.span_le]
  intro z hz
  rcases Set.mem_insert_iff.mp hz with hz | hz
  · rw [hz]
    obtain ⟨m, _, hm⟩ := completeIdentityFirstGraphConductorIdeal_left K n h i
    exact ⟨m, hm⟩
  · rw [Set.mem_singleton_iff.mp hz]
    obtain ⟨m, _, hm⟩ := completeIdentityFirstGraphConductorIdeal_right K n h i
    exact ⟨m, hm⟩

/-- The conductor's closed vanishing locus is contained in the unchanged original node locus. -/
theorem completeIdentityFirstGraphConductorIdeal_zeroLocus :
    PrimeSpectrum.zeroLocus (completeIdentityFirstGraphConductorIdeal K n h i : Set (B)) ⊆
      PrimeSpectrum.zeroLocus (coordinateIdeal (e) : Set (B)) := by
  rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  exact completeIdentityFirstGraphConductorIdeal_node K n h i

end FLT.Mazur.PolygonInfinitesimalStages
