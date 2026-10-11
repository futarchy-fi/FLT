/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalPositiveCharts
public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalEndCharts
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalPositiveCharts
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalEndCharts

/-!
# Global descent on every complete component of both cyclic chains

Both affine restrictions determine the whole projective component, including
the first attachment and the last horizontal charts at positive equality depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w

local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The entire first cyclic chain recovers its prescribed projective maps. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_first_component (j : Fin s) :
    (Z ⟨j.val + 1, by omega⟩).left ≫ d = F ⟨j.val + 1, by omega⟩ := by
  apply pushout.hom_ext
  · by_cases hj : j.val < s - 1
    · exact zeroEqualityPositiveCycleGlobalDesc_positive_first_left
        hπ data D s hs hstart hk hp hpos F w ⟨j.val, hj⟩
    · have he : j.val + 1 = s := by omega
      simpa only [he, ProjectiveLine.left, ProjectiveLine.right] using
        zeroEqualityPositiveCycleGlobalDesc_terminal_first_chart
          hπ data D s hs hstart hk hp hpos F w
  · by_cases hj : j.val = 0
    · have he : j.val + 1 = 1 := by omega
      simpa only [he, Fin.one_eq_mk_of_lt (by omega : 1 < 2 * s + 2),
        ProjectiveLine.left, ProjectiveLine.right] using
        zeroEqualityPositiveCycleGlobalDesc_attachment_first_chart
          hπ data D s hs hstart hk hp hpos F w
    · have H := zeroEqualityPositiveCycleGlobalDesc_positive_first_right
        hπ data D s hs hstart hk hp hpos F w ⟨j.val - 1, by omega⟩
      dsimp only at H
      have he' : j.val - 1 + 2 = j.val + 1 := by omega
      simpa only [he', ProjectiveLine.left, ProjectiveLine.right] using H

/-- The entire second cyclic chain recovers its prescribed projective maps. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_second_component (j : Fin s) :
    (Z ⟨2 * s + 1 - j.val, by omega⟩).left ≫ d = F ⟨2 * s + 1 - j.val, by omega⟩ := by
  apply pushout.hom_ext
  · by_cases hj : j.val = 0
    · simpa only [hj, Nat.sub_zero, ProjectiveLine.left, ProjectiveLine.right] using
        zeroEqualityPositiveCycleGlobalDesc_attachment_second_chart
          hπ data D s hs hstart hk hp hpos F w
    · have he : j.val - 1 + 1 = j.val := by omega
      have H := zeroEqualityPositiveCycleGlobalDesc_positive_second_left
        hπ data D s hs hstart hk hp hpos F w ⟨j.val - 1, by omega⟩
      dsimp only at H
      simpa only [he, ProjectiveLine.left, ProjectiveLine.right] using H
  · by_cases hj : j.val < s - 1
    · exact zeroEqualityPositiveCycleGlobalDesc_positive_second_right
        hπ data D s hs hstart hk hp hpos F w ⟨j.val, hj⟩
    · have hi : 2 * s + 1 - j.val = s + 2 := by omega
      simpa only [hi, ProjectiveLine.left, ProjectiveLine.right] using
        zeroEqualityPositiveCycleGlobalDesc_terminal_second_chart
          hπ data D s hs hstart hk hp hpos F w

end FLT.Mazur.WeierstrassDividedDepth
