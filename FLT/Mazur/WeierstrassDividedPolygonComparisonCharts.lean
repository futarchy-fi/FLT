/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwistedClosingInclusion
public import FLT.Mazur.WeierstrassDividedArithmeticFirstRetainedBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioTriangle
public import FLT.Mazur.WeierstrassDividedArithmeticPositiveLabeledCompatibility

/-!
# Concrete polygon comparisons on every original label

The initial, infinity and retained comparisons satisfy their full original
edge equations. The terminal comparison is constructed separately; no closing
compatibility is asserted here.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "Y" => arithmeticFactorRatioPolygon π m W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "A" => arithmeticLabeledAtlasObject hπ data H m (j + 1) hj
local notation "e" => twistedArithmeticAtlasIso hπ data H m j hj u hu

/-- Actual chart maps to the prescribed polygon, with its original retained index convention. -/
def arithmeticPolygonComparisonChart (i : ArithmeticChartLabel (j + 1)) : A i ⟶ Y := by
  let _ := Fact.mk
    (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m H.scale_div)
  exact match i with
  | .infinity => arithmeticFactorRatioLabeledInfinityMap data H hπ m (j + 1) hj
  | .initial b => arithmeticFactorRatioLabeledInitialMap data H hπ m (j + 1) hj b
  | .retained a b => arithmeticStartOneRetainedMap hπ data H m (j + 1) hj a b
  | .terminal => (e .terminal).hom ≫
      PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega) 0

local notation "F" => arithmeticPolygonComparisonChart hπ data H m j hj u hu

/-- Both original infinity equations hold for the constructed comparisons. -/
theorem arithmeticPolygonComparisonChart_infinity :
    arithmeticInitialInfinityCompatible hπ data H m (j + 1) hj F :=
  arithmeticFactorRatioTriangle_compatible hπ data H m (j + 1) hj F rfl (fun _ ↦ rfl)

omit [IsBezout R] in
/-- Both first-edge equations use the original puncture and its entire inverse parameter. -/
theorem arithmeticPolygonComparisonChart_initial :
    arithmeticPositiveInitialCompatible hπ data H m j hj F := by
  intro b
  let d := data ⟨0, Nat.zero_lt_succ n⟩
  let E := arithmeticInitialPunctureIso π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
  apply (cancel_epi E.hom).mp
  dsimp only [arithmeticPolygonComparisonChart]
  rw [← Category.assoc, arithmeticInitialPunctureIso_boundary,
    arithmeticFactorRatioLabeledInitialMap_first_retained hπ data H m (j + 1) hj
      (Nat.zero_lt_succ j), Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticStartOneRetainedMap_first hπ data H m (j + 1) hj (Nat.zero_lt_succ j)]

omit [IsBezout R] in
/-- Every consecutive retained equation uses the full depth recurrence and root corrections. -/
theorem arithmeticPolygonComparisonChart_adjacent :
    arithmeticPositiveAdjacentCompatible hπ data H m j hj F := by
  intro a ha b
  exact arithmeticStartOneRetainedMap_adjacent hπ data H m (j + 1) hj a ha b

/-- Global compatibility of these concrete charts reduces exactly to the two closing equations. -/
theorem arithmeticPolygonComparisonChart_compatible_iff :
    (∀ a b, pullback.fst
      (arithmeticLabeledAtlasMap hπ data H m (j + 1) hj a)
      (arithmeticLabeledAtlasMap hπ data H m (j + 1) hj b) ≫ F a =
      pullback.snd (arithmeticLabeledAtlasMap hπ data H m (j + 1) hj a)
        (arithmeticLabeledAtlasMap hπ data H m (j + 1) hj b) ≫ F b) ↔
      arithmeticPositiveTerminalCompatible hπ data H m j hj F := by
  rw [arithmeticPositiveLabeled_compatible_iff]
  exact ⟨fun h ↦ h.2.2.2, fun h ↦
    ⟨arithmeticPolygonComparisonChart_infinity hπ data H m j hj u hu,
      arithmeticPolygonComparisonChart_initial hπ data H m j hj u hu,
      arithmeticPolygonComparisonChart_adjacent hπ data H m j hj u hu, h⟩⟩

end FLT.Mazur.WeierstrassDividedDepth
