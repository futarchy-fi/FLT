/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedLineExt
public import FLT.Mazur.WeierstrassDividedFinalAdjacentConicBranches
public import FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLineBranches
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterSplitComparison

/-!
# Arbitrary-target uniqueness on every positive-start retained node

Earlier conics use their full split branches. The terminal conic uses its
original parameter opens with the actual nonzero divided constant. This also
handles the first retained pair and the four-component cycle.
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
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

section Earlier
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

include h in
/-- Every earlier first full retained node is determined by cyclic agreement. -/
theorem positiveEqualityCycleComponent_retained_first_hom_ext :
    G₁ ≫ transport ≫ f = G₁ ≫ transport ≫ g := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · have H := congrArg (fun q => ProjectiveLine.left K ≫ q)
      (positiveEqualityCycleComponent_adjacent_hom_ext hπ data D s hs hstart hk hp f g h j 0)
    simpa only [finalAdjacentComponent_positive_first_left_nodeBranch_assoc hπ data D
      s hs hk j (by omega)] using H
  · have H := positiveEqualityCycleComponent_retained_first_line_hom_ext
      hπ data D s hs hstart hk hp f g h j.val (by omega)
    simpa only [middleParameterLineBranch_eq_split c hc] using H

include h in
/-- Every earlier second full retained node is determined by cyclic agreement. -/
theorem positiveEqualityCycleComponent_retained_second_hom_ext :
    G₂ ≫ transport ≫ f = G₂ ≫ transport ≫ g := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · have H := congrArg (fun q => Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ q)
      (positiveEqualityCycleComponent_adjacent_hom_ext hπ data D s hs hstart hk hp f g h j 1)
    simpa only [finalAdjacentComponent_positive_second_left_nodeBranch_assoc hπ data D
      s hs hk j (by omega)] using H
  · have H := positiveEqualityCycleComponent_retained_second_line_hom_ext
      hπ data D s hs hstart hk hp f g h j.val (by omega)
    simpa only [middleParameterLineBranch_eq_split c hc] using H

end Earlier

local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "G₁" => olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk
local notation "G₂" => olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk

include h in
/-- The final first full node is determined even when no adjacent component precedes it. -/
theorem positiveEqualityCycleComponent_terminal_first_hom_ext : G₁ ≫ f = G₁ ≫ g := by
  apply middleParameter_hom_ext c
  · have H := congrArg (fun q => equalityTerminalFirstNodeParameter data D s hs hk hp ≫ q)
      (positiveEqualityCycleComponent_terminal_component_hom_ext
        hπ data D s hs hstart hk hp f g h)
    simpa only [equalityTerminalFirstNodeParameter_branch_assoc hπ data D s hs hk hp
      (by omega)] using H
  · have H := positiveEqualityCycleComponent_retained_first_line_hom_ext
      hπ data D s hs hstart hk hp f g h s (by omega)
    simpa only [olderGlobalResidueFirstNode_zero_transport_assoc
      hπ data D s (s - s) hs _ _ _ (Nat.sub_self s)] using H

include h in
/-- The final second full node is determined even when no adjacent component precedes it. -/
theorem positiveEqualityCycleComponent_terminal_second_hom_ext : G₂ ≫ f = G₂ ≫ g := by
  apply middleParameter_hom_ext c
  · have H := congrArg (fun q => Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
        equalityTerminalSecondNodeParameter data D s hs hk hp ≫ q)
      (positiveEqualityCycleComponent_terminal_component_hom_ext
        hπ data D s hs hstart hk hp f g h)
    simpa only [equalityTerminalSecondNodeParameter_branch_assoc hπ data D s hs hk hp
      (by omega)] using H
  · have H := positiveEqualityCycleComponent_retained_second_line_hom_ext
      hπ data D s hs hstart hk hp f g h s (by omega)
    simpa only [olderGlobalResidueSecondNode_zero_transport_assoc
      hπ data D s (s - s) hs _ _ _ (Nat.sub_self s)] using H

end FLT.Mazur.WeierstrassDividedDepth
