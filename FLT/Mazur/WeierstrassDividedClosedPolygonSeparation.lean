/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedInitialRetainedIntersection
public import FLT.Mazur.WeierstrassDividedPolygonInfinitySeparation

/-!
# Separation in the actual closed polygon comparison

The complete original infinity chart avoids every retained and terminal
image. Both original initial images avoid the terminal image as well.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "F" => arithmeticClosedPolygonMap hπ data H j hj u hu
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "e" => twistedArithmeticAtlasIso hπ data H 0 j hj u hu
local notation "N" => arithmeticClosedTerminalNormalization data H j hj u hu
local notation "U" => arithmeticLabeledOpenCover hπ data H 0 (j + 1) hj

local notation "c" => @PolygonInfinitesimal.chart Q _ τ hn (2 * (j + 1) + 3)
  (Nat.le_trans (Nat.le_succ 2) (Nat.le_add_left 3 (2 * (j + 1))))

/-- The full initial comparison stays within its prescribed polygon chart. -/
theorem arithmeticClosedInitial_range_subset (b : Bool) :
    Set.range (G (.initial b)) ⊆ Set.range (c (initialPolygonIndex (j + 1) b)) := by
  let _ := hn
  rw [arithmeticClosedInitial_normalized hπ data H j hj u hu b]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- The whole original retained comparison keeps its exact cyclic label. -/
theorem arithmeticClosedRetained_range_subset (idx : Fin (j + 1)) (b : Bool) :
    Set.range (G (.retained idx b)) ⊆ Set.range (c (retainedPolygonIndex (j + 1) idx b)) := by
  let _ := hn
  rw [arithmeticClosedRetained_normalized hπ data H j hj u hu idx b]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- The simultaneous correction retains the original terminal label zero. -/
theorem arithmeticClosedTerminal_range_subset : Set.range (G .terminal) ⊆ Set.range (c 0) := by
  let _ := hn
  rintro _ ⟨x, rfl⟩
  exact ⟨((e .terminal).hom ≫ (N).hom) x, rfl⟩

/-- No original initial point is identified with a terminal point. -/
theorem arithmeticClosedInitialTerminal_disjoint (b : Bool) :
    Disjoint (Set.range (G (.initial b))) (Set.range (G .terminal)) := by
  let _ := hn
  exact Disjoint.mono (arithmeticClosedInitial_range_subset hπ data H j hj u hu b)
    (arithmeticClosedTerminal_range_subset hπ data H j hj u hu)
    (initialPolygon_terminal_disjoint Q τ (j + 1) (Nat.zero_lt_succ j) b)

/-- The entire original infinity label is separated from every retained comparison. -/
theorem arithmeticClosedInfinityRetained_disjoint (idx : Fin (j + 1)) (b : Bool) :
    Disjoint (Set.range (G .infinity)) (Set.range (G (.retained idx b))) := by
  let _ := hn
  change Disjoint (Set.range (arithmeticFactorRatioLabeledInfinityMap data H hπ 0 (j + 1) hj)) _
  rw [arithmeticClosedInfinityPolygonMap_range]
  exact Disjoint.mono_right (arithmeticClosedRetained_range_subset hπ data H j hj u hu idx b)
    (initialPolygon_infinity_retained_disjoint Q τ (j + 1) idx b)

/-- The entire original infinity and simultaneously corrected terminal images are disjoint. -/
theorem arithmeticClosedInfinityTerminal_disjoint :
    Disjoint (Set.range (G .infinity)) (Set.range (G .terminal)) := by
  let _ := hn
  change Disjoint (Set.range (arithmeticFactorRatioLabeledInfinityMap data H hπ 0 (j + 1) hj)) _
  rw [arithmeticClosedInfinityPolygonMap_range]
  exact Disjoint.mono_right (arithmeticClosedTerminal_range_subset hπ data H j hj u hu)
    (initialPolygon_infinity_terminal_disjoint Q τ (j + 1) (Nat.zero_lt_succ j))

end FLT.Mazur.WeierstrassDividedDepth
