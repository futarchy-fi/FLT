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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "g" => globalInitialTensorChart hπ data K (1 + s) (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K 0 (by omega) s (by omega)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => positiveEqualityInitialTensorDesc hπ data D s hs hstart hk F w

/-- The full initial overlap is compatible with its first strictly interior retained chart. -/
theorem positiveEqualityInitialInteriorTensor_compatible (hs0 : 0 < s) :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫
      positiveEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp ⟨0, hs0⟩ F w := by
  apply initialRetained_compatible_of_branch_restrictions hπ data D (by omega)
    hstart (by omega) s (by omega) d
    (positiveEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp ⟨0, hs0⟩ F w)
    (F 1) (F ⟨2 * s + 3, by omega⟩)
  · simpa only [Category.assoc] using
      positiveEqualityInitialTensorDesc_first_parameter hπ data D s hs hstart hk F w
  · simpa only [Category.assoc] using
      positiveEqualityInitialTensorDesc_second_parameter hπ data D s hs hstart hk F w
  · rw [← residueMiddleFirstNodeChart_lineBranch_assoc D start hstart (by omega)
      (Data.b3 (data ⟨1, by omega⟩)) (Data.b4 (data ⟨1, by omega⟩))
      (Data.b6 (data ⟨1, by omega⟩)) (Data.factor3 _) (Data.factor4 _)
      (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
        D (start + 1) (by omega) _ (Data.factor6 _)))]
    have H := positiveEqualityCycleInteriorTensorDesc_first
      hπ data D s hs hstart hk hp ⟨0, hs0⟩ F w
    simp only [Fin.val_mk, Nat.add_zero] at H
    rw [H]
    exact positiveEqualityCycleInteriorFirstLocalDesc_line data D s hs hk ⟨0, hs0⟩ F w
  · rw [← residueMiddleSecondNodeChart_lineBranch_assoc D start hstart (by omega)
      (Data.b3 (data ⟨1, by omega⟩)) (Data.b4 (data ⟨1, by omega⟩))
      (Data.b6 (data ⟨1, by omega⟩)) (Data.factor3 _) (Data.factor4 _)
      (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
        D (start + 1) (by omega) _ (Data.factor6 _)))]
    have H := positiveEqualityCycleInteriorTensorDesc_second
      hπ data D s hs hstart hk hp ⟨0, hs0⟩ F w
    simp only [Fin.val_mk, Nat.add_zero] at H
    rw [H]
    exact positiveEqualityCycleInteriorSecondLocalDesc_line data D s hs hk ⟨0, hs0⟩ F w

end FLT.Mazur.WeierstrassDividedDepth
