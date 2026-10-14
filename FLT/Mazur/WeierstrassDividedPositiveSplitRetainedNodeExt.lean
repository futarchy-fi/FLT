/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedLineExt
public import FLT.Mazur.WeierstrassDividedFinalSplitBranchCharts
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterSplitComparison

/-!
# Arbitrary-target uniqueness on every positive-start retained node

Every retained conic uses its full split branches, including the terminal one.
The original initial components supply the first retained horizontal branches.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
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
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

variable (j : Fin (s + 1))
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j.val + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)

include h in
/-- Every original first full retained node is determined by cyclic agreement. -/
theorem positiveSplitCycleComponent_retained_first_hom_ext :
    G₁ ≫ transport ≫ f = G₁ ≫ transport ≫ g := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · have H := congrArg (fun q => ProjectiveLine.left K ≫ q)
      (positiveSplitCycleComponent_tail_hom_ext hπ data D s hs hstart hk hp f g h j 0)
    simpa only [finalBranchComponent_positive_first_left_nodeBranch_assoc hπ data D
      s hs hk hp j (by omega)] using H
  · have H := positiveSplitCycleComponent_retained_first_line_hom_ext
      hπ data D s hs hstart hk hp f g h j.val (by omega)
    simpa only [middleParameterLineBranch_eq_split c hc] using H

include h in
/-- Every original second full retained node is determined by cyclic agreement. -/
theorem positiveSplitCycleComponent_retained_second_hom_ext :
    G₂ ≫ transport ≫ f = G₂ ≫ transport ≫ g := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · have H := congrArg (fun q => Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ q)
      (positiveSplitCycleComponent_tail_hom_ext hπ data D s hs hstart hk hp f g h j 1)
    simpa only [finalBranchComponent_positive_second_left_nodeBranch_assoc hπ data D
      s hs hk hp j (by omega)] using H
  · have H := positiveSplitCycleComponent_retained_second_line_hom_ext
      hπ data D s hs hstart hk hp f g h j.val (by omega)
    simpa only [middleParameterLineBranch_eq_split c hc] using H


end FLT.Mazur.WeierstrassDividedDepth
