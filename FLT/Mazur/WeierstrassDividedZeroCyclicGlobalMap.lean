/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceDesc
public import FLT.Mazur.WeierstrassDividedZeroCyclicStandardMaps

/-!
# A global map from the original stage to the independent standard five-gon

The five full node comparisons descend through the actual source pushouts.
No retained edge is reduced and every normalized smoothing may drift.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "Y" => arithmeticZeroCyclicStandard hπ data H hj u hu m
local notation "f" => arithmeticZeroCyclicSeedToStandard hπ data H hj u hu m

/-- Reindex the five full seed maps by their concrete source vertices. -/
def arithmeticZeroCyclicStandardSeedMap (i : ZeroCyclicVertex) :
    PolygonSmoothing.chart Q ((S).parameter m i) ⟶ Y :=
  match i with
  | .terminal => f 0
  | .retained false => f 1
  | .retained true => f 4
  | .initial false => f 2
  | .initial true => f 3

local notation "g" => arithmeticZeroCyclicStandardSeedMap hπ data H m hj u hu

/-- Every exact original edge is compatible with the corresponding whole-node comparison. -/
@[reassoc] theorem arithmeticZeroCyclicStandardSeedMap_edge (i : ZeroCyclicVertex) :
    leftBranchOpen Q ((S).parameter m i) ≫ g i =
      (punctureSpecIso ((S).edge m i)).hom ≫
        rightBranchOpen Q ((S).parameter m (zeroCyclicSuccessor i)) ≫
          g (zeroCyclicSuccessor i) := by
  rcases i with _ | (_ | _) | (_ | _)
  · exact arithmeticZeroCyclicSeedToStandard_edge hπ data H hj u hu m 0
  · exact arithmeticZeroCyclicSeedToStandard_edge hπ data H hj u hu m 1
  · exact arithmeticZeroCyclicSeedToStandard_edge hπ data H hj u hu m 4
  · exact arithmeticZeroCyclicSeedToStandard_edge hπ data H hj u hu m 2
  · exact arithmeticZeroCyclicSeedToStandard_edge hπ data H hj u hu m 3

/-- The actual original corrected global stage maps to the independent standard five-gon. -/
def arithmeticZeroCyclicGlobalMap :
    simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu ⟶ Y :=
  arithmeticZeroCyclicSourceDesc hπ data H m hj u hu g
    (arithmeticZeroCyclicStandardSeedMap_edge hπ data H m hj u hu)

/-- The global map retains each full original seed-node comparison. -/
@[reassoc] theorem arithmeticZeroCyclicGlobalMap_chart (i : ZeroCyclicVertex) :
    arithmeticZeroCyclicSourceChart hπ data H m hj u hu i ≫
      arithmeticZeroCyclicGlobalMap hπ data H m hj u hu = g i :=
  arithmeticZeroCyclicSourceDesc_chart hπ data H m hj u hu g
    (arithmeticZeroCyclicStandardSeedMap_edge hπ data H m hj u hu) i

/-- The standard enumeration recovers exactly the existing five whole-node maps. -/
theorem arithmeticZeroCyclicStandardSeedMap_index (i : Fin 5) :
    g (zeroCyclicIndex i) = f i := by
  fin_cases i <;> rfl

end FLT.Mazur.WeierstrassDividedDepth
