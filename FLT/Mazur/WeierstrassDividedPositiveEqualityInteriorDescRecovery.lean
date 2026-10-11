/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorConicCharts
public import FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedLineCharts
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialDescRecovery
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterSplitComparison
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps

/-!
# Earlier positive-start descent recovers the original full nodes

For the actual cyclic component family, both chosen descents are exactly
the complete original retained inclusions, including the first retained pair.
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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
variable (j : Fin s)
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

local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveEqualityCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp
local notation "t" => WeierstrassDilatation.residueTangentUnit D

/-- Descent on the actual family recovers the whole first retained node inclusion. -/
theorem positiveEqualityCycleInteriorFirstLocalDesc_original :
    positiveEqualityCycleInteriorFirstLocalDesc data D s hs hk j F w = G₁ ≫ transport := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · rw [positiveEqualityCycleInteriorFirstLocalDesc_conic,
      positiveEqualityCycleComponent_interior_first_conic_chart]
  · apply middleNode_cancel_chartScaling (t)⁻¹
    rw [positiveEqualityCycleInteriorFirstLocalDesc_line,
      positiveEqualityCycleComponent_retained_first_line_chart
        hπ data D s hs hstart hk hp j.val (by omega)]
    rw [middleParameterLineBranch_eq_split c hc]

/-- The opposite descended map recovers its entire original retained node inclusion. -/
theorem positiveEqualityCycleInteriorSecondLocalDesc_original :
    positiveEqualityCycleInteriorSecondLocalDesc data D s hs hk j F w = G₂ ≫ transport := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · rw [positiveEqualityCycleInteriorSecondLocalDesc_conic,
      positiveEqualityCycleComponent_interior_second_conic_chart]
  · apply middleNode_cancel_chartScaling (-t)⁻¹
    rw [positiveEqualityCycleInteriorSecondLocalDesc_line,
      positiveEqualityCycleComponent_retained_second_line_chart
        hπ data D s hs hstart hk hp j.val (by omega)]
    rw [middleParameterLineBranch_eq_split c hc]

end FLT.Mazur.WeierstrassDividedDepth
