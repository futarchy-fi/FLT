/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialBranchCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialTensorBranches
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialTensorBranches
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitLocalMaps

/-!
# The initial cyclic descent agrees on the full first interior tensor overlap

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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "g" => globalInitialTensorChart hπ data K (1 + s) (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K 0 (by omega) s (by omega)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => positiveSplitInitialTensorDesc hπ data D s hs hstart hk F w

/-- The full initial overlap is compatible with its first retained chart, even at s = 0. -/
theorem positiveSplitInitialRetainedTensor_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫
      positiveSplitCycleRetainedTensorDesc hπ data D s hs hstart hk hp ⟨0, by omega⟩ F w := by
  apply initialRetained_compatible_of_branch_restrictions hπ data D (by omega)
    hstart (by omega) s (by omega) d
    (positiveSplitCycleRetainedTensorDesc hπ data D s hs hstart hk hp ⟨0, by omega⟩ F w)
    (F 1) (F ⟨2 * s + 4, by omega⟩)
  · simpa only [Category.assoc] using
      positiveSplitInitialTensorDesc_first_parameter hπ data D s hs hstart hk F w
  · simpa only [Category.assoc] using
      positiveSplitInitialTensorDesc_second_parameter hπ data D s hs hstart hk F w
  · rw [← residueMiddleFirstNodeChart_lineBranch_assoc D start hstart (by omega)
      (Data.b3 (data ⟨1, by omega⟩)) (Data.b4 (data ⟨1, by omega⟩))
      (Data.b6 (data ⟨1, by omega⟩)) (Data.factor3 _) (Data.factor4 _)
      (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
        D (start + 1) (by omega) _ (Data.factor6 _)))]
    have H := positiveSplitCycleRetainedTensorDesc_first
      hπ data D s hs hstart hk hp ⟨0, by omega⟩ F w
    simp only [Fin.val_mk, Nat.add_zero] at H
    rw [H]
    exact positiveSplitCycleFirstLocalDesc_line data D s hs hp ⟨0, by omega⟩ F w
  · rw [← residueMiddleSecondNodeChart_lineBranch_assoc D start hstart (by omega)
      (Data.b3 (data ⟨1, by omega⟩)) (Data.b4 (data ⟨1, by omega⟩))
      (Data.b6 (data ⟨1, by omega⟩)) (Data.factor3 _) (Data.factor4 _)
      (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
        D (start + 1) (by omega) _ (Data.factor6 _)))]
    have H := positiveSplitCycleRetainedTensorDesc_second
      hπ data D s hs hstart hk hp ⟨0, by omega⟩ F w
    simp only [Fin.val_mk, Nat.add_zero] at H
    rw [H]
    exact positiveSplitCycleSecondLocalDesc_line data D s hs hp ⟨0, by omega⟩ F w

end FLT.Mazur.WeierstrassDividedDepth
