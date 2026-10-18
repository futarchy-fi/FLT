/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedTensorMaps
public import FLT.Mazur.WeierstrassDividedRevisedInitialBoundary
public import FLT.Mazur.WeierstrassDividedRevisedClosingAtlasIdentification

/-!
# Every original first-order labeled chart in the revised polygon

The initial and infinity maps retain their complete polynomial factor ratios.
The retained and terminal maps use the constructed common closing correction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
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
local notation "Q" => Quotient R π 1
local notation "t" => parameter R π 1
local notation "A" => arithmeticLabeledAtlasObject hπ data H 1 (j + 1) hj
local notation "E" => arithmeticFirstResidualAtlasIso hπ data H j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu

/-- The complete actual first-order chart family in the independent cyclic target. -/
def arithmeticFirstOriginalRevisedChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ arithmeticRevisedPolygon data H 1 j hj u hu :=
  match i with
  | .initial b => arithmeticOriginalRevisedInitialMap data H 1 j hj u hu b
  | .infinity => arithmeticOriginalRevisedTensorInfinityMap data H 1 j hj u hu
  | .retained a b => arithmeticFirstOriginalRevisedRetainedMap hπ data H j hj u hu a b
  | .terminal => (E .terminal).hom ≫ d

local notation "F" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu

/-- Each original consecutive retained edge commutes on its entire source. -/
theorem arithmeticFirstOriginalRevisedChart_adjacent :
    arithmeticPositiveAdjacentCompatible hπ data H 1 j hj F := by
  intro a ha b
  exact arithmeticFirstOriginalRevisedRetainedMap_adjacent hπ data H j hj u hu a ha b

/-- Both original initial edges commute, including the single-retained-node case. -/
theorem arithmeticFirstOriginalRevisedChart_initial :
    arithmeticPositiveInitialCompatible hπ data H 1 j hj F := by
  intro b
  let d₀ := data ⟨0, Nat.zero_lt_succ n⟩
  let P := arithmeticInitialPunctureIso π 1 W (π ^ 1)
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
  apply (cancel_epi P.hom).mp
  dsimp only [arithmeticFirstOriginalRevisedChart]
  rw [← Category.assoc, arithmeticInitialPunctureIso_boundary,
    arithmeticFirstOriginalRevisedInitialMap_first_retained hπ data H j hj u hu,
    Category.assoc, Iso.hom_inv_id_assoc]

local notation "r" => arithmeticOriginalClosingBoundary data H 1 j hj
local notation "G" => arithmeticFirstOriginalRevisedClosingMap data H j hj u hu hπ

/-- The actual full closing-pair restrictions give the original terminal Laurent equation. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedChart_closing (b : Bool) :
    r b ≫ F .terminal = leftBranchOpen Q t ≫ F (.retained ⟨j, by omega⟩ b) := by
  change r b ≫ (E .terminal).hom ≫ d =
    leftBranchOpen Q t ≫ arithmeticFirstOriginalRevisedRetainedMap hπ data H j hj u hu _ b
  rw [← arithmeticFirstOriginalRevisedClosingMap_terminal_atlas hπ data H j hj u hu b,
    ← arithmeticFirstOriginalRevisedRetainedMap_closing hπ data H j hj u hu b,
    ← Category.assoc, ← Category.assoc, pushout.condition]

/-- Both full standard terminal punctures commute with their original inverse parameters. -/
theorem arithmeticFirstOriginalRevisedChart_terminal :
    arithmeticPositiveTerminalCompatible hπ data H 1 j hj F := by
  intro b
  let P := terminalArithmeticPunctureIso data 1 j hj H.a1_unit
    (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b
  apply (cancel_epi P.hom).mp
  dsimp only [P]
  rw [← Category.assoc]
  erw [terminalArithmeticPunctureIso_boundary data 1 j hj H.a1_unit
    (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b]
  change r b ≫ F .terminal = P.hom ≫ (P.inv ≫ leftBranchOpen Q t) ≫
    F (.retained ⟨j, by omega⟩ b)
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact arithmeticFirstOriginalRevisedChart_closing hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
