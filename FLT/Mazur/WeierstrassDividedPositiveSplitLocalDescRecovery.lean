/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedConicCharts
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedLineCharts
public import FLT.Mazur.WeierstrassDividedPositiveSplitLocalMaps
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterSplitComparison
import all FLT.Mazur.WeierstrassDividedPositiveSplitLocalMaps

/-!
# Strict positive-start descent recovers every original full retained node

For the actual cyclic component family, both chosen descents are exactly
the complete original retained inclusions, including both the first and
terminal retained pairs.
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
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
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

/-- The original scheme component maps satisfy the full cyclic endpoint equations. -/
theorem positiveSplitCycleComponent_scheme_endpoints (i : Fin (2 * s + 5)) :
    ProjectiveLine.zero K ≫ (Z i).left =
      ProjectiveLine.infinity K ≫ (Z (PolygonPinching.next (by omega) i)).left :=
  congrArg Over.Hom.left
    (positiveSplitCycleComponent_endpoints hπ data D s hs hstart hk hp i)

local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveSplitCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp
local notation "t" => WeierstrassDilatation.residueTangentUnit D

/-- Descent on the actual family recovers the whole first retained node inclusion. -/
theorem positiveSplitCycleFirstLocalDesc_original :
    positiveSplitCycleFirstLocalDesc data D s hs hp j F w = G₁ ≫ transport := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · rw [positiveSplitCycleFirstLocalDesc_conic,
      positiveSplitCycleComponent_retained_first_conic_chart]
  · apply middleNode_cancel_chartScaling (t)⁻¹
    rw [positiveSplitCycleFirstLocalDesc_line,
      positiveSplitCycleComponent_retained_first_line_chart
        hπ data D s hs hstart hk hp j.val (by omega)]
    rw [middleParameterLineBranch_eq_split c hc]

/-- The opposite descended map recovers its entire original retained node inclusion. -/
theorem positiveSplitCycleSecondLocalDesc_original :
    positiveSplitCycleSecondLocalDesc data D s hs hp j F w = G₂ ≫ transport := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · rw [positiveSplitCycleSecondLocalDesc_conic,
      positiveSplitCycleComponent_retained_second_conic_chart]
  · apply middleNode_cancel_chartScaling (-t)⁻¹
    rw [positiveSplitCycleSecondLocalDesc_line,
      positiveSplitCycleComponent_retained_second_line_chart
        hπ data D s hs hstart hk hp j.val (by omega)]
    rw [middleParameterLineBranch_eq_split c hc]

end FLT.Mazur.WeierstrassDividedDepth
