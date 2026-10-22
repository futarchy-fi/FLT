/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Exact stage requirements for flexible retained formulas

These are bounds for the existing sum/reflected formulas, not obstructions to
all possible addition laws. The near-terminal adjacent range is already sharp
for those formulas. Separated pairs have a distinct feasible range.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDividedDepth

/-- Beyond the two boundary depths, the adjacent formula bounds have this exact range. -/
theorem arithmeticAdjacentFlexibleStage_iff (i depth : ℕ)
    (hlo : 2 * (i + 3) + 2 ≤ depth) :
    (min (2 * i + 3) (depth - (2 * i + 3)) ≤ i + 3 ∧
      min (2 * i + 4) (depth - (2 * i + 4)) ≤ i + 3) ↔
        depth ≤ 3 * i + 6 := by
  omega

/-- The separated formula bounds simplify exactly, including the creation-one edge case. -/
theorem arithmeticSeparatedFlexibleStage_iff (i j depth : ℕ) :
    max (min (i + j + 2) (depth - (i + j + 2)))
      (min (i + j + 3) (depth - (i + j + 3))) ≤ j + 2 ↔
        depth ≤ i + 2 * j + 4 + (if i = 0 then 1 else 0) := by
  split_ifs <;> omega

/-- Past both boundary depths, the exceptional creation-one case disappears. -/
theorem arithmeticSeparatedBeyondBoundaryStage_iff (i j depth : ℕ)
    (hlo : 2 * (j + 2) + 2 ≤ depth) :
    max (min (i + j + 2) (depth - (i + j + 2)))
      (min (i + j + 3) (depth - (i + j + 3))) ≤ j + 2 ↔
        depth ≤ i + 2 * j + 4 := by
  rw [arithmeticSeparatedFlexibleStage_iff]
  split_ifs <;> omega

/-- The smallest stage containing the next input chart and all three output depths. -/
def arithmeticFlexiblePairStage (i j depth : ℕ) : ℕ :=
  max (j + 3) (max (min (i + j + 2) (depth - (i + j + 2)))
    (max (min (i + j + 3) (depth - (i + j + 3)))
      (min (i + j + 4) (depth - (i + j + 4)))))

/-- The stage is exactly the conjunction needed by the three actual transfer formulas. -/
theorem arithmeticFlexiblePairStage_le_iff (i j depth k : ℕ) :
    arithmeticFlexiblePairStage i j depth ≤ k ↔
      j + 3 ≤ k ∧
      max (min (i + j + 2) (depth - (i + j + 2)))
        (max (min (i + j + 3) (depth - (i + j + 3)))
          (min (i + j + 4) (depth - (i + j + 4)))) ≤ k := by
  unfold arithmeticFlexiblePairStage
  omega

/-- The flexible stage never exceeds the old unreflected sum-depth stage. -/
theorem arithmeticFlexiblePairStage_le_sum (i j depth : ℕ) :
    arithmeticFlexiblePairStage i j depth ≤ i + j + 4 := by
  unfold arithmeticFlexiblePairStage
  omega

/-- Near the middle, every output fits the first stage after the later transfer. -/
theorem arithmeticFlexiblePairStage_eq_next (i j depth : ℕ)
    (hdepth : depth ≤ 2 * (j + 3) + 1) :
    arithmeticFlexiblePairStage i j depth = j + 3 := by
  unfold arithmeticFlexiblePairStage
  omega

/-- In the reflection range the largest output depth is the unshifted reflection. -/
theorem arithmeticFlexiblePairStage_eq_reflected (i j depth : ℕ)
    (href : depth ≤ 2 * (i + j + 2)) :
    arithmeticFlexiblePairStage i j depth = max (j + 3) (depth - (i + j + 2)) := by
  unfold arithmeticFlexiblePairStage
  omega

end FLT.Mazur.WeierstrassDividedDepth
