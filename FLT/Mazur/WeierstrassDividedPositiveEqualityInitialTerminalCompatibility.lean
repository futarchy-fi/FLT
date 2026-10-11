/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialBranchCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorBranches
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorBranches
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps

/-!
# Full initial overlap compatibility for the four-component equality cycle

Both local descents are the pullbacks of the actual fixed atlas family.
Their four proved branch restrictions give equality on the entire adjacent
fiber product, at every later common retained stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "g" => globalInitialTensorChart hπ data K (1 + 0) (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K 0 (by omega) 0 (by omega)
variable {Y : Scheme.{u}}
  (F : Fin (2 * 0 + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => positiveEqualityInitialTensorDesc hπ data D 0 hs hstart hk F w

/-- With no interior chart, the initial chart meets the full terminal retained chart. -/
theorem positiveEqualityInitialTerminalTensor_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫
      positiveEqualityCycleTerminalTensorDesc hπ data D 0 hs hstart hk hp F w := by
  apply initialRetained_compatible_of_branch_restrictions hπ data D hs
    hstart hk 0 hs d
    (positiveEqualityCycleTerminalTensorDesc hπ data D 0 hs hstart hk hp F w)
    (F 1) (F ⟨3, by omega⟩)
  · simpa only [Category.assoc] using
      positiveEqualityInitialTensorDesc_first_parameter hπ data D 0 hs hstart hk F w
  · simpa only [Category.assoc] using
      positiveEqualityInitialTensorDesc_second_parameter hπ data D 0 hs hstart hk F w
  · rw [← residueMiddleFirstNodeChart_parameterLineBranch_assoc]
    have H := positiveEqualityCycleTerminalTensorDesc_first
      hπ data D 0 hs hstart hk hp F w
    simp only [Nat.add_zero] at H
    rw [H]
    exact positiveEqualityCycleTerminalFirstDesc_line data D 0 hs hk hp F w
  · rw [← residueMiddleSecondNodeChart_parameterLineBranch_assoc]
    have H := positiveEqualityCycleTerminalTensorDesc_second
      hπ data D 0 hs hstart hk hp F w
    simp only [Nat.add_zero] at H
    rw [H]
    exact positiveEqualityCycleTerminalSecondDesc_line data D 0 hs hk hp F w

end FLT.Mazur.WeierstrassDividedDepth
