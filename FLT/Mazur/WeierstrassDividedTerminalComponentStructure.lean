/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalZeroComponents
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# The full terminal projective components are over the residue field

The structure equality is checked on both complete affine charts of each
projective line. It therefore retains the actual coefficient structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 1) hj)

/-- The first positive-depth component is over the original coefficient field. -/
@[reassoc] theorem terminalFirstComponent_structure (hk0 : 0 < start + j) :
    terminalFirstComponent hπ data D j hj hk0 hk hp ≫ p = ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ terminalFirstComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [terminalFirstComponent_left_assoc, terminalConicFirstParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫ terminalFirstComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [terminalFirstComponent_right_assoc, terminalConicSecondBranch, Category.assoc,
      terminalNodeChart_structure, PolygonCyclicAtlas.secondBranch_toBase,
      ProjectiveLine.right_toBase]

/-- The second positive-depth component is over the original coefficient field. -/
@[reassoc] theorem terminalSecondComponent_structure (hk0 : 0 < start + j) :
    terminalSecondComponent hπ data D j hj hk0 hk hp ≫ p = ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ terminalSecondComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [terminalSecondComponent_left_assoc, terminalConicSecondParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫ terminalSecondComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [terminalSecondComponent_right_assoc, terminalConicFirstBranch, Category.assoc,
      terminalNodeChart_structure, PolygonCyclicAtlas.firstBranch_toBase,
      ProjectiveLine.right_toBase]

/-- The first scale-one component is over the original coefficient field. -/
@[reassoc] theorem terminalZeroFirstComponent_structure (hk0 : start + j = 0) :
    terminalZeroFirstComponent hπ data D j hj hk0 hk hp ≫ p = ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ terminalZeroFirstComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [terminalZeroFirstComponent_left_assoc, terminalZeroConicFirstParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫ terminalZeroFirstComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [terminalZeroFirstComponent_right_assoc, terminalConicSecondBranch, Category.assoc,
      terminalNodeChart_structure, PolygonCyclicAtlas.secondBranch_toBase,
      ProjectiveLine.right_toBase]

/-- The second scale-one component is over the original coefficient field. -/
@[reassoc] theorem terminalZeroSecondComponent_structure (hk0 : start + j = 0) :
    terminalZeroSecondComponent hπ data D j hj hk0 hk hp ≫ p = ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ terminalZeroSecondComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [terminalZeroSecondComponent_left_assoc, terminalZeroConicSecondParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫ terminalZeroSecondComponent hπ data D j hj hk0 hk hp ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [terminalZeroSecondComponent_right_assoc, terminalConicFirstBranch, Category.assoc,
      terminalNodeChart_structure, PolygonCyclicAtlas.firstBranch_toBase,
      ProjectiveLine.right_toBase]

end FLT.Mazur.WeierstrassDividedDepth
