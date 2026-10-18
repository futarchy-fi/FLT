/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialRetainedReflection
public import FLT.Mazur.WeierstrassDividedRevisedTargetLabels

/-!
# Disjoint full original images in the first-order revised target

The full infinity edge is contained in both initial nodes, which excludes
all retained nodes. Positive retained depth separates both initial nodes
from the terminal node, so infinity is also separated from the terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "p" => arithmeticRevisedPolygonParameter data H 1 j hj u hu
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "c" => arithmeticRevisedPolygonInitialChart data H 1 j hj u hu
local notation "r" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu

omit [IsBezout R] in
/-- The entire initial comparison stays in its prescribed full target node. -/
theorem arithmeticFirstRevisedInitial_range_subset (b : Bool) :
    Set.range (G (.initial b)) ⊆ Set.range (c b) := by
  rw [arithmeticFirstRevisedInitial_normalized]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

omit [IsBezout R] in
/-- The actual corrected retained comparison keeps its cyclic target label. -/
theorem arithmeticFirstRevisedRetained_range_subset (idx : Fin (j + 1)) (b : Bool) :
    Set.range (G (.retained idx b)) ⊆ Set.range (r idx b) := by
  rw [arithmeticFirstRevisedRetained_normalized]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

omit [IsBezout R] in
/-- The common terminal correction retains the entire terminal node label. -/
theorem arithmeticFirstRevisedTerminal_range_subset :
    Set.range (G .terminal) ⊆ Set.range d := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(arithmeticFirstResidualAtlasIso hπ data H j hj u hu .terminal).hom x, rfl⟩

omit [IsBezout R] in
/-- The full original infinity edge lies in both complete target initial nodes. -/
theorem arithmeticFirstRevisedInfinity_range_subset (b : Bool) :
    Set.range (G .infinity) ⊆ Set.range (c b) := by
  change Set.range (arithmeticOriginalRevisedTensorInfinityMap data H 1 j hj u hu) ⊆ _
  rw [arithmeticOriginalRevisedTensorInfinityMap_range,
    ← arithmeticRevisedPolygon_infinity_range data H 1 j hj u hu b]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

attribute [local irreducible] arithmeticRevisedPolygon
  PolygonVariableSmoothing.scheme PolygonVariableSmoothing.chartWithParameter

omit [IsDomain R] [IsBezout R] in
/-- Each full initial target node is disjoint from the common terminal target node. -/
theorem arithmeticRevisedInitialTerminal_disjoint (b : Bool) :
    Disjoint (Set.range (c b)) (Set.range d) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact arithmeticRevisedInitialTerminal_ne data H 1 j hj u hu b x y hy.symm

omit [IsBezout R] in
/-- No original initial point is identified with a terminal point. -/
theorem arithmeticFirstRevisedInitialTerminal_disjoint (b : Bool) :
    Disjoint (Set.range (G (.initial b))) (Set.range (G .terminal)) :=
  Disjoint.mono (arithmeticFirstRevisedInitial_range_subset hπ data H j hj u hu b)
    (arithmeticFirstRevisedTerminal_range_subset hπ data H j hj u hu)
    (arithmeticRevisedInitialTerminal_disjoint data H j hj u hu b)

omit [IsBezout R] in
/-- Infinity has no point in any retained image because it lies in both initial target nodes. -/
theorem arithmeticFirstRevisedInfinityRetained_disjoint (idx : Fin (j + 1)) (b : Bool) :
    Disjoint (Set.range (G .infinity)) (Set.range (G (.retained idx b))) := by
  apply Set.disjoint_left.mpr
  intro z hz hr
  obtain ⟨y, hy⟩ := arithmeticFirstRevisedRetained_range_subset hπ data H j hj u hu idx b hr
  have hb : ∀ e : Bool, e = b := by
    intro e
    obtain ⟨x, hx⟩ := arithmeticFirstRevisedInfinity_range_subset hπ data H j hj u hu e hz
    have hl := arithmeticRevisedInitialRetained_labels data H 1 j hj u hu idx e b
      x y (hx.trans hy.symm)
    exact hl.2
  exact Bool.false_ne_true ((hb false).trans (hb true).symm)

omit [IsBezout R] in
/-- The entire original infinity image is disjoint from the corrected terminal image. -/
theorem arithmeticFirstRevisedInfinityTerminal_disjoint :
    Disjoint (Set.range (G .infinity)) (Set.range (G .terminal)) :=
  Disjoint.mono (arithmeticFirstRevisedInfinity_range_subset hπ data H j hj u hu false)
    (arithmeticFirstRevisedTerminal_range_subset hπ data H j hj u hu)
    (arithmeticRevisedInitialTerminal_disjoint data H j hj u hu false)

end FLT.Mazur.WeierstrassDividedDepth
