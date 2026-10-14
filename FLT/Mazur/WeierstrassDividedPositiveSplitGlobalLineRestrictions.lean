/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedLineCharts
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterSplitComparison
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedLineCharts
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveSplitLocalMaps

/-!
# Global descent on the complete horizontal retained branches

All retained conic constants vanish by strict depth, including the terminal
retained pair in the five-component cycle.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveSplitCycleGlobalDesc hπ data D s hs hstart hk hp F w
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
/-- The entire first horizontal chart recovers its prescribed cyclic component. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_retained_first_line
    (j : ℕ) (hj : j ≤ s) :
    ProjectiveLine.left K ≫ (Z ⟨j + 1, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨j + 1, by omega⟩ := by
  rw [positiveSplitCycleComponent_retained_first_line_chart_assoc
    hπ data D s hs hstart hk hp j hj]
  let e := data (Fin.mk (j + 1) (by omega))
  have hc : residue R (Data.b6 e) = 0 :=
    (residue_eq_zero_iff _).mpr
      (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
        (Data.b6 e) (Data.factor6 e))
  rw [middleParameterLineBranch_eq_split _ hc]
  rw [positiveSplitCycleGlobalDesc_positive_first
    hπ data D s hs hstart hk hp F w ⟨j, by omega⟩]
  exact positiveSplitCycleFirstLocalDesc_line data D s hs hp ⟨j, by omega⟩ F w

/-- The entire second horizontal chart recovers its prescribed cyclic component. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_retained_second_line
    (j : ℕ) (hj : j ≤ s) :
    ProjectiveLine.right K ≫ (Z ⟨2 * s + 4 - j, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨2 * s + 4 - j, by omega⟩ := by
  rw [positiveSplitCycleComponent_retained_second_line_chart_assoc
    hπ data D s hs hstart hk hp j hj]
  let e := data (Fin.mk (j + 1) (by omega))
  have hc : residue R (Data.b6 e) = 0 :=
    (residue_eq_zero_iff _).mpr
      (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
        (Data.b6 e) (Data.factor6 e))
  rw [middleParameterLineBranch_eq_split _ hc]
  rw [positiveSplitCycleGlobalDesc_positive_second
    hπ data D s hs hstart hk hp F w ⟨j, by omega⟩]
  exact positiveSplitCycleSecondLocalDesc_line data D s hs hp ⟨j, by omega⟩ F w

end FLT.Mazur.WeierstrassDividedDepth
