/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLineBranches
public import FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedLineCharts
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterSplitComparison
import all FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedLineCharts
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps

/-!
# Global descent on the complete horizontal retained branches

Earlier conic constants vanish by depth. The terminal branch retains its
actual constant, including the four-component cycle.
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
  (hp : 2 * (start + s + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveEqualityCycleGlobalDesc hπ data D s hs hstart hk hp F w
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
/-- The entire first horizontal chart recovers its prescribed cyclic component. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_retained_first_line
    (j : ℕ) (hj : j ≤ s) :
    ProjectiveLine.left K ≫ (Z ⟨j + 1, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨j + 1, by omega⟩ := by
  by_cases hjs : j < s
  · rw [positiveEqualityCycleComponent_retained_first_line_chart_assoc
      hπ data D s hs hstart hk hp j hj]
    let e := data (Fin.mk (j + 1) (by omega))
    have hc : residue R (Data.b6 e) = 0 :=
      (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
          (Data.b6 e) (Data.factor6 e))
    rw [middleParameterLineBranch_eq_split _ hc]
    rw [positiveEqualityCycleGlobalDesc_positive_first
      hπ data D s hs hstart hk hp F w ⟨j, hjs⟩]
    exact positiveEqualityCycleInteriorFirstLocalDesc_line data D s hs hk ⟨j, hjs⟩ F w
  · have hje : j = s := by omega
    subst j
    have H := positiveEqualityCycleComponent_retained_first_line_chart
      hπ data D s hs hstart hk hp s (by omega)
    rw [olderGlobalResidueFirstNode_zero_transport hπ data D
      s (s - s) hs _ _ _ (Nat.sub_self s)] at H
    rw [← Category.assoc, H]
    simp only [Category.assoc]
    rw [positiveEqualityCycleGlobalDesc_terminal_first,
      positiveEqualityCycleTerminalFirstDesc_line]

/-- The entire second horizontal chart recovers its prescribed cyclic component. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_retained_second_line
    (j : ℕ) (hj : j ≤ s) :
    ProjectiveLine.right K ≫ (Z ⟨2 * s + 3 - j, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨2 * s + 3 - j, by omega⟩ := by
  by_cases hjs : j < s
  · rw [positiveEqualityCycleComponent_retained_second_line_chart_assoc
      hπ data D s hs hstart hk hp j hj]
    let e := data (Fin.mk (j + 1) (by omega))
    have hc : residue R (Data.b6 e) = 0 :=
      (residue_eq_zero_iff _).mpr
        (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
          (Data.b6 e) (Data.factor6 e))
    rw [middleParameterLineBranch_eq_split _ hc]
    rw [positiveEqualityCycleGlobalDesc_positive_second
      hπ data D s hs hstart hk hp F w ⟨j, hjs⟩]
    exact positiveEqualityCycleInteriorSecondLocalDesc_line data D s hs hk ⟨j, hjs⟩ F w
  · have hje : j = s := by omega
    subst j
    have H := positiveEqualityCycleComponent_retained_second_line_chart
      hπ data D s hs hstart hk hp s (by omega)
    rw [olderGlobalResidueSecondNode_zero_transport hπ data D
      s (s - s) hs _ _ _ (Nat.sub_self s)] at H
    rw [← Category.assoc, H]
    simp only [Category.assoc]
    rw [positiveEqualityCycleGlobalDesc_terminal_second,
      positiveEqualityCycleTerminalSecondDesc_line]
    congr 2
    apply Fin.ext
    dsimp
    omega

end FLT.Mazur.WeierstrassDividedDepth
