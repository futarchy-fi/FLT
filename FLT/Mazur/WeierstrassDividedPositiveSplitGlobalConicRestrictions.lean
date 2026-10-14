/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedConicCharts
public import FLT.Mazur.ProjectiveLineScaledAffineOverlap
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveSplitLocalMaps

/-!
# Global descent on both complete retained conic charts

The opposite conic coordinate keeps its original sign. Cancelling the
negative affine scaling recovers the unmodified projective chart.
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
/-- The first full retained conic chart recovers its reversed cyclic component. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_retained_first_conic (j : Fin (s + 1)) :
    ProjectiveLine.right K ≫ (Z ⟨j.val + 2, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨j.val + 2, by omega⟩ := by
  rw [positiveSplitCycleComponent_retained_first_conic_chart_assoc,
    positiveSplitCycleGlobalDesc_positive_first,
    positiveSplitCycleFirstLocalDesc_conic]

/-- The opposite full conic chart recovers its component after cancelling its negative scale. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_retained_second_conic (j : Fin (s + 1)) :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 4 - (j.val + 1), by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 4 - (j.val + 1), by omega⟩ := by
  apply (cancel_epi (ProjectiveLine.chartScalingIso K (-1)).hom).mp
  change ProjectiveLine.chartScaling K (-1) ≫ _ = ProjectiveLine.chartScaling K (-1) ≫ _
  rw [← middleNode_negativeParameter_eq_scaling]
  rw [positiveSplitCycleComponent_retained_second_conic_chart_assoc,
    positiveSplitCycleGlobalDesc_positive_second,
    positiveSplitCycleSecondLocalDesc_conic]

end FLT.Mazur.WeierstrassDividedDepth
