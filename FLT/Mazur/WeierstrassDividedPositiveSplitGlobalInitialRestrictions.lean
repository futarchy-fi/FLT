/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialTensorBranches
public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialCharts
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialTensorBranches
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily
import all FLT.Mazur.WeierstrassDividedInitialConicParameters
import all FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart

/-!
# Global cyclic descent on the original initial tensor and full conic charts

The two node restrictions determine the whole incidence line and both full conic
parameters. These identities retain the original slope and tangent orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "V" => finiteInitialTensorAtlasIso hπ data K (s + 1) hs
local notation "N₁" => residueFullFirstNodeChart D start hstart (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N₂" => residueFullSecondNodeChart D start hstart (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

local notation "E" => residueFiberIso D start hstart (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "d" => positiveSplitCycleGlobalDesc hπ data D s hs hstart hk hp F w
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)

local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp

/-- The glued global map recovers the whole original initial tensor descent. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_initial_tensor :
    globalInitialTensorChart hπ data K (s + 1) hs ≫ d =
      positiveSplitInitialTensorDesc hπ data D s hs hstart hk F w := by
  rw [← globalInitialTensorChart_eq_index, Category.assoc,
    positiveSplitCycleGlobalDesc_atlas]
  have H := positiveSplitCycleAtlasFamily_initial hπ data D s hs hstart hk hp F w
  simp only [Fin.succ_mk] at *
  rw [H]
  rfl

/-- The first original full conic parameter is the right chart of its cyclic component. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_initial_first_chart :
    ProjectiveLine.right K ≫ (Z 1).left ≫ d = ProjectiveLine.right K ≫ F 1 := by
  rw [positiveSplitCycleComponent_initial_first_chart_assoc]
  simp only [initialGlobalConicFirstParameter, initialGlobalConic,
    initialGlobalResidueFiberChart, Category.assoc]
  rw [positiveSplitCycleGlobalDesc_initial_tensor]
  exact positiveSplitInitialTensorDesc_first_parameter hπ data D s hs hstart hk F w

/-- The opposite entire initial conic parameter keeps its original orientation. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_initial_second_chart :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 4, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 4, by omega⟩ := by
  rw [positiveSplitCycleComponent_initial_second_chart_assoc]
  simp only [initialGlobalConicSecondParameter, initialGlobalConic,
    initialGlobalResidueFiberChart, Category.assoc]
  rw [positiveSplitCycleGlobalDesc_initial_tensor]
  exact positiveSplitInitialTensorDesc_second_parameter hπ data D s hs hstart hk F w

end FLT.Mazur.WeierstrassDividedDepth
