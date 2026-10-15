/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphAlgebra
public import FLT.Mazur.PolygonFirstNodeWeightedConductor

/-!
# A uniform conductor for the full original first-order graph

The same positive power of each node coordinate sends every function in the
actual source-target graph algebra into the original node. These bounds are
uniform over the entire graph, not separately chosen for each function.
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
local notation "L" => (S)[T;T⁻¹]
local notation "C" => firstNodeBranchSubalgebra (R)
local notation "β" => firstNodeBranchPair (R)
local notation "D" => completeIdentityFirstActionNodeDefect K n h i
local notation "G" => completeIdentityFirstGraphAlgebra K n h i
local notation "x" => leftCoordinate (e)
local notation "y" => rightCoordinate (e)

/-- Clearing just the two original coordinate errors clears the whole original graph. -/
theorem completeIdentityFirstGraphAlgebra_conductor_of_coordinates (w : B)
    (hx : (D) (x) * (β) w ∈ (C)) (hy : (D) (y) * (β) w ∈ (C))
    (z : (L) × (L)) (hz : z ∈ (G)) : z * (β) w ∈ (C) := by
  rw [← completeIdentityFirstErrorAlgebra_eq_graph] at hz
  obtain ⟨a, b, c, rfl⟩ := completeIdentityFirstErrorAlgebra_normalForm K n h i z hz
  rw [add_mul, add_mul, mul_assoc b.val, mul_assoc c.val]
  exact (C).add_mem ((C).add_mem ((C).mul_mem a.property ⟨w, rfl⟩)
    ((C).mul_mem b.property hx)) ((C).mul_mem c.property hy)

/-- Two independently constructed power bounds combine into a uniform graph bound. -/
theorem completeIdentityFirstGraphAlgebra_power_conductor (w : B)
    (hx : ∃ m : ℕ, 0 < m ∧ (D) (x) * (β) (w ^ m) ∈ (C))
    (hy : ∃ m : ℕ, 0 < m ∧ (D) (y) * (β) (w ^ m) ∈ (C)) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ (G), z * (β) (w ^ m) ∈ (C) := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, _, hyb⟩ := hy
  refine ⟨a + b, by omega, ?_⟩
  apply completeIdentityFirstGraphAlgebra_conductor_of_coordinates K n h i
  · rw [pow_add w a b, map_mul, ← mul_assoc]
    exact (C).mul_mem hxa ⟨w ^ b, rfl⟩
  · rw [pow_add w a b, map_mul,
      mul_comm ((β) (w ^ a)) ((β) (w ^ b)), ← mul_assoc]
    exact (C).mul_mem hyb ⟨w ^ a, rfl⟩

/-- A single positive left power sends the entire original graph into the original node. -/
theorem completeIdentityFirstGraphAlgebra_left_conductor :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ (G), z * (β) ((x) ^ m) ∈ (C) :=
  completeIdentityFirstGraphAlgebra_power_conductor K n h i (x)
    (firstNodePair_annihilator_left_conductor (R) _
      (completeIdentityFirstActionNodeDefect_parameter K n h i (x)))
    (firstNodePair_annihilator_left_conductor (R) _
      (completeIdentityFirstActionNodeDefect_parameter K n h i (y)))

/-- A single positive right power has the same full graph-clearing property. -/
theorem completeIdentityFirstGraphAlgebra_right_conductor :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ (G), z * (β) ((y) ^ m) ∈ (C) :=
  completeIdentityFirstGraphAlgebra_power_conductor K n h i (y)
    (firstNodePair_annihilator_right_conductor (R) _
      (completeIdentityFirstActionNodeDefect_parameter K n h i (x)))
    (firstNodePair_annihilator_right_conductor (R) _
      (completeIdentityFirstActionNodeDefect_parameter K n h i (y)))

end FLT.Mazur.PolygonInfinitesimalStages
