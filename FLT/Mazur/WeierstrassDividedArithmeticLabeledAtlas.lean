/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledCoverage

/-!
# A finite labeled open cover of each original arithmetic stage

The label records infinity, the terminal node, either full initial node,
or a retained depth and its small/opposite branch. No pointwise choices
enter the chart maps, and the infinity chart is the original one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- The labels of the complete arithmetic cover, retaining both roots at each depth. -/
inductive ArithmeticChartLabel (k : ℕ)
  | infinity
  | terminal
  | initial (opposite : Bool)
  | retained (depth : Fin k) (opposite : Bool)
  deriving DecidableEq, Fintype

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "dₖ" => data (Fin.mk k (Nat.lt_succ_of_le hk))

/-- The actual original chart schemes, indexed by their geometric labels. -/
def arithmeticLabeledAtlasObject : ArithmeticChartLabel k → Scheme
  | .infinity => globalTensorAtlasObject hπ data Q k hk 0
  | .terminal => Spec (.of (NodalFiber.Coordinate
      (WeierstrassDilatation.arithmeticTerminalSmoothing π m W (π ^ (start + k))
        (Data.b3 dₖ) (Data.b4 dₖ) (Data.b6 dₖ) H.a1_unit (H.scale k) H.a2_div
          (H.b4_div _) (H.b6_div _))))
  | .initial _ => Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ start))))
  | .retained _ _ => Spec (.of (PolygonSmoothing.ChartRing (parameter R π m)))

/-- All original coefficient and depth information is retained in these labeled chart maps. -/
def arithmeticLabeledAtlasMap (i : ArithmeticChartLabel k) :
    arithmeticLabeledAtlasObject hπ data H m k hk i ⟶
      finiteGlobalArithmeticStage hπ data k hk m :=
  match i with
  | .infinity => arithmeticTensorAtlasMap hπ data m k hk 0
  | .terminal => arithmeticLabeledTerminalChart hπ data H m k hk
  | .initial label => arithmeticLabeledInitialChart hπ data H m k hk label
  | .retained a label => arithmeticLabeledRetainedChart hπ data H m k hk a label

instance arithmeticLabeledAtlasMap_isOpenImmersion (i : ArithmeticChartLabel k) :
    IsOpenImmersion (arithmeticLabeledAtlasMap hπ data H m k hk i) := by
  cases i <;> dsimp only [arithmeticLabeledAtlasMap] <;> infer_instance

/-- Every arithmetic stage point belongs to one of the explicitly labeled original charts. -/
theorem arithmeticLabeledAtlas_cover (z : finiteGlobalArithmeticStage hπ data k hk m) :
    ∃ i x, arithmeticLabeledAtlasMap hπ data H m k hk i x = z := by
  obtain ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨b, x, hx⟩ | ⟨a, b, x, hx⟩ :=
    arithmeticLabeledCharts_cover hπ data H m k hk z
  · exact ⟨.infinity, x, hx⟩
  · exact ⟨.terminal, x, hx⟩
  · exact ⟨.initial b, x, hx⟩
  · exact ⟨.retained a b, x, hx⟩

/-- The full finite labeled atlas as an actual open cover of the original arithmetic stage. -/
def arithmeticLabeledOpenCover : (finiteGlobalArithmeticStage hπ data k hk m).OpenCover where
  I₀ := ArithmeticChartLabel k
  X := arithmeticLabeledAtlasObject hπ data H m k hk
  f := arithmeticLabeledAtlasMap hπ data H m k hk
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨arithmeticLabeledAtlas_cover hπ data H m k hk,
      fun i => arithmeticLabeledAtlasMap_isOpenImmersion hπ data H m k hk i⟩

end FLT.Mazur.WeierstrassDividedDepth
