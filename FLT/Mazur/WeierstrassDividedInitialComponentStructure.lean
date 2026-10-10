/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialProjectiveComponents
public import FLT.Mazur.WeierstrassDividedAdjacentParameterStructure

/-!
# The complete initial components preserve the original residue field

The two full projective maps are over the residue field because their actual
conic parameters and first retained lines preserve that same coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (r : ℕ) (hr : 1 + r ≤ n)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (1 + r) hr)

/-- The complete first initial projective component is over the original residue field. -/
@[reassoc] theorem initialGlobalFirstComponent_structure :
    initialGlobalFirstComponent hπ data D h1 hstart hk r hr ≫ p =
      ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        initialGlobalFirstComponent hπ data D h1 hstart hk r hr ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [initialGlobalFirstComponent_left_assoc, initialGlobalConicFirstParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫
        initialGlobalFirstComponent hπ data D h1 hstart hk r hr ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [initialGlobalFirstComponent_right_assoc, olderGlobalMiddleFirstLine_structure,
      ProjectiveLine.chartScaling_toBase, ProjectiveLine.right_toBase]

/-- The complete opposite initial component retains the same coefficient structure. -/
@[reassoc] theorem initialGlobalSecondComponent_structure :
    initialGlobalSecondComponent hπ data D h1 hstart hk r hr ≫ p =
      ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        initialGlobalSecondComponent hπ data D h1 hstart hk r hr ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [initialGlobalSecondComponent_left_assoc, initialGlobalConicSecondParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫
        initialGlobalSecondComponent hπ data D h1 hstart hk r hr ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [initialGlobalSecondComponent_right_assoc, olderGlobalMiddleSecondLine_structure,
      ProjectiveLine.chartScaling_toBase, ProjectiveLine.right_toBase]

end FLT.Mazur.WeierstrassDividedDepth
