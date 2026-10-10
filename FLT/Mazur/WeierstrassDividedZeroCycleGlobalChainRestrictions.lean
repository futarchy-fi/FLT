/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalPositiveCharts
public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalEndCharts
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalPositiveCharts
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalEndCharts

/-!
# Global descent on every complete component of both cyclic chains

Both affine restrictions determine the whole projective component, including
the first attachment and terminal component when the chain length is zero.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F w

local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

/-- The entire first cyclic chain recovers its prescribed projective maps. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_first_component (j : Fin (s + 1)) :
    (Z ⟨j.val + 1, by omega⟩).left ≫ d = F ⟨j.val + 1, by omega⟩ := by
  apply pushout.hom_ext
  · by_cases hj : j.val < s
    · exact zeroSplitCycleGlobalDesc_positive_first_left
        hπ data D s hs hstart hp F w ⟨j.val, hj⟩
    · have he : j.val = s := by omega
      simpa only [he, ProjectiveLine.left, ProjectiveLine.right] using
        zeroSplitCycleGlobalDesc_terminal_first_chart hπ data D s hs hstart hp F w
  · by_cases hj : j.val = 0
    · have he : j = 0 := Fin.ext hj
      subst j
      exact zeroSplitCycleGlobalDesc_attachment_first_chart hπ data D s hs hstart hp F w
    · have H := zeroSplitCycleGlobalDesc_positive_first_right
        hπ data D s hs hstart hp F w ⟨j.val - 1, by omega⟩
      dsimp only at H
      have he' : j.val - 1 + 2 = j.val + 1 := by omega
      simpa only [he', ProjectiveLine.left, ProjectiveLine.right] using H

/-- The entire second cyclic chain recovers its prescribed projective maps. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_second_component (j : Fin (s + 1)) :
    (Z ⟨2 * s + 2 - j.val, by omega⟩).left ≫ d = F ⟨2 * s + 2 - j.val, by omega⟩ := by
  apply pushout.hom_ext
  · by_cases hj : j.val = 0
    · have he : j = 0 := Fin.ext hj
      subst j
      exact zeroSplitCycleGlobalDesc_attachment_second_chart hπ data D s hs hstart hp F w
    · have he : j.val - 1 + 1 = j.val := by omega
      have H := zeroSplitCycleGlobalDesc_positive_second_left
        hπ data D s hs hstart hp F w ⟨j.val - 1, by omega⟩
      dsimp only at H
      simpa only [he, ProjectiveLine.left, ProjectiveLine.right] using H
  · by_cases hj : j.val < s
    · exact zeroSplitCycleGlobalDesc_positive_second_right
        hπ data D s hs hstart hp F w ⟨j.val, hj⟩
    · have he : j.val = s := by omega
      have hi : 2 * s + 2 - j.val = s + 2 := by omega
      simpa only [hi, ProjectiveLine.left, ProjectiveLine.right] using
        zeroSplitCycleGlobalDesc_terminal_second_chart hπ data D s hs hstart hp F w

end FLT.Mazur.WeierstrassDividedDepth
