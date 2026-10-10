/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalBranchChains
public import FLT.Mazur.WeierstrassDividedConicParameterTransport

/-!
# The first chain components retain their complete start-zero affine charts

This includes the stage-zero terminal pair and every later adjacent pair.
The equalities transport only the target stage index.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 1 (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : 0 + 1 + s ≤ n) hs (by omega))
local notation "P₁" => olderGlobalZeroConicFirstParameter hπ data D 0 (by omega)
  s (by omega) (by omega) (by omega)
local notation "P₂" => olderGlobalZeroConicSecondParameter hπ data D 0 (by omega)
  s (by omega) (by omega) (by omega)

/-- The first chain starts with the complete original first affine conic parameter. -/
@[reassoc] theorem finalBranchComponent_zero_first_left :
    ProjectiveLine.left K ≫
        (finalBranchComponent hπ data D s hs hk hp 0 0).left =
      (E).hom ≫ P₁ ≫ transport := by
  cases s with
  | zero =>
    simp only [finalBranchComponent, Fin.val_zero, lt_self_iff_false, dite_false]
    change ProjectiveLine.left K ≫ finalTerminalComponent hπ data D 0 hs hk hp 0 = _
    rw [finalTerminalComponent_zero_depth hπ data D 0 hs hk hp (by omega)]
    change ProjectiveLine.left K ≫ terminalZeroFirstComponent hπ data D 0 hs
      (by omega) hk hp = _
    rw [terminalZeroFirstComponent_left, terminalZeroConicFirstParameter_retained]
    simp only [eqToHom_refl, Category.comp_id]
  | succ t =>
    rw [finalBranchComponent, dite_eq_left (show (0 : Fin (t + 1 + 1)).val < t + 1 by
      exact Nat.zero_lt_succ t)]
    change ProjectiveLine.left K ≫ finalAdjacentComponent hπ data D (t + 1) hs hk 0 0 = _
    rw [finalAdjacentComponent]
    simp only [Fin.val_zero]
    rw [orderedAdjacentComponent_zero_depth hπ data D 0 _ _ _ _ _ _ (by omega)]
    change ProjectiveLine.left K ≫
      adjacentZeroFirstComponent hπ data D 0 _ _ _ _ _ t _ ≫ _ = _
    rw [adjacentZeroFirstComponent_left_assoc, adjacentZeroFirstParameter_transport]
    simp only [Category.assoc, eqToHom_trans]

/-- The other chain starts with the complete original opposite affine conic parameter. -/
@[reassoc] theorem finalBranchComponent_zero_second_left :
    ProjectiveLine.left K ≫
        (finalBranchComponent hπ data D s hs hk hp 0 1).left =
      (E).hom ≫ P₂ ≫ transport := by
  cases s with
  | zero =>
    simp only [finalBranchComponent, Fin.val_zero, lt_self_iff_false, dite_false]
    change ProjectiveLine.left K ≫ finalTerminalComponent hπ data D 0 hs hk hp 1 = _
    rw [finalTerminalComponent_zero_depth hπ data D 0 hs hk hp (by omega)]
    change ProjectiveLine.left K ≫ terminalZeroSecondComponent hπ data D 0 hs
      (by omega) hk hp = _
    rw [terminalZeroSecondComponent_left, terminalZeroConicSecondParameter_retained]
    simp only [eqToHom_refl, Category.comp_id]
  | succ t =>
    rw [finalBranchComponent, dite_eq_left (show (0 : Fin (t + 1 + 1)).val < t + 1 by
      exact Nat.zero_lt_succ t)]
    change ProjectiveLine.left K ≫ finalAdjacentComponent hπ data D (t + 1) hs hk 0 1 = _
    rw [finalAdjacentComponent]
    simp only [Fin.val_zero]
    rw [orderedAdjacentComponent_zero_depth hπ data D 0 _ _ _ _ _ _ (by omega)]
    change ProjectiveLine.left K ≫
      adjacentZeroSecondComponent hπ data D 0 _ _ _ _ _ t _ ≫ _ = _
    rw [adjacentZeroSecondComponent_left_assoc, adjacentZeroSecondParameter_transport]
    simp only [Category.assoc, eqToHom_trans]

end FLT.Mazur.WeierstrassDividedDepth
