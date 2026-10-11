/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorConicCharts
public import FLT.Mazur.ProjectiveLineScaledAffineOverlap
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps

/-!
# Global descent on both complete interior conic charts

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
  (hp : 2 * (start + s + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveEqualityCycleGlobalDesc hπ data D s hs hstart hk hp F w
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
/-- The first full interior conic chart recovers its reversed cyclic component. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_interior_first_conic (j : Fin s) :
    ProjectiveLine.right K ≫ (Z ⟨j.val + 2, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨j.val + 2, by omega⟩ := by
  rw [positiveEqualityCycleComponent_interior_first_conic_chart_assoc,
    positiveEqualityCycleGlobalDesc_positive_first,
    positiveEqualityCycleInteriorFirstLocalDesc_conic]

/-- The opposite full conic chart recovers its component after cancelling its negative scale. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_interior_second_conic (j : Fin s) :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 2 - j.val, by omega⟩ := by
  apply (cancel_epi (ProjectiveLine.chartScalingIso K (-1)).hom).mp
  change ProjectiveLine.chartScaling K (-1) ≫ _ = ProjectiveLine.chartScaling K (-1) ≫ _
  rw [← middleNode_negativeParameter_eq_scaling]
  rw [positiveEqualityCycleComponent_interior_second_conic_chart_assoc,
    positiveEqualityCycleGlobalDesc_positive_second,
    positiveEqualityCycleInteriorSecondLocalDesc_conic]

end FLT.Mazur.WeierstrassDividedDepth
