/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderParameterNodeBranches
public import FLT.Mazur.WeierstrassDividedLaurentTerminalProjectiveComponent

/-!
# Original positive-depth node branches in the complete equality-depth terminal line

Both node parameters map into the actual terminal projective component. The
opposite parameter retains its sign, while the entire conic and Laurent gluing
is retained in the target component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) = depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "q₁" => laurentConicComponentFirstParameter D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "q₂" => laurentConicComponentSecondParameter D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "J" => laurentConicComponentProjectiveIso D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "F" => laurentTerminalProjectiveComponent hπ data D j hj hk hp

/-- The actual first parameter open in the complete terminal projective line. -/
def equalityTerminalFirstNodeParameter : Spec (.of (ConicParameterOpen c)) ⟶
    ProjectiveLine.scheme K := q₁ ≫ (J).inv

/-- The actual opposite parameter open in the complete terminal projective line. -/
def equalityTerminalSecondNodeParameter : Spec (.of (ConicParameterOpen c)) ⟶
    ProjectiveLine.scheme K := q₂ ≫ (J).inv

/-- The first parameter origin is the first endpoint of the complete terminal line. -/
@[reassoc] theorem equalityTerminalFirstNodeParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      equalityTerminalFirstNodeParameter data D j hj hk hp = ProjectiveLine.zero K := by
  rw [equalityTerminalFirstNodeParameter, laurentConicComponentFirstParameter_origin_assoc]
  rw [← laurentConicComponentProjectiveIso_zero D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The second parameter origin is the other endpoint of the same complete terminal line. -/
@[reassoc] theorem equalityTerminalSecondNodeParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      equalityTerminalSecondNodeParameter data D j hj hk hp = ProjectiveLine.infinity K := by
  rw [equalityTerminalSecondNodeParameter, laurentConicComponentSecondParameter_origin_assoc]
  rw [← laurentConicComponentProjectiveIso_infinity D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [IsBezout R]

/-- The first node's conic branch is the original terminal project's full parameter open. -/
@[reassoc] theorem equalityTerminalFirstNodeParameter_branch (hk0 : 0 < start + j) :
    equalityTerminalFirstNodeParameter data D j hj hk hp ≫ F =
      middleParameterConicBranch c ≫
        olderGlobalResidueFirstNode hπ data D j hj 0 hj hk0 hk := by
  rw [equalityTerminalFirstNodeParameter, laurentTerminalProjectiveComponent,
    Category.assoc, Iso.inv_hom_id_assoc,
    olderGlobalResidueFirstNode_parameterConicBranch]
  simp only [laurentConicComponentFirstParameter, Category.assoc,
    laurentTerminalComponentMap_conic]
  rw [laurentTerminalOriginalConic_positive hπ data D j hj hk hk0]
  unfold olderGlobalMiddleConicFirstParameter olderGlobalMiddleConic
  rw [olderGlobalTensorChart_zero_retention]
  rfl

/-- The opposite node retains the negative parameter on the same terminal projective line. -/
@[reassoc] theorem equalityTerminalSecondNodeParameter_branch (hk0 : 0 < start + j) :
    Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
        equalityTerminalSecondNodeParameter data D j hj hk hp ≫ F =
      middleParameterConicBranch c ≫
        olderGlobalResidueSecondNode hπ data D j hj 0 hj hk0 hk := by
  rw [equalityTerminalSecondNodeParameter, laurentTerminalProjectiveComponent,
    Category.assoc, Iso.inv_hom_id_assoc,
    olderGlobalResidueSecondNode_parameterConicBranch]
  simp only [laurentConicComponentSecondParameter, Category.assoc,
    laurentTerminalComponentMap_conic]
  rw [laurentTerminalOriginalConic_positive hπ data D j hj hk hk0]
  unfold olderGlobalMiddleConicSecondParameter olderGlobalMiddleConic
  rw [olderGlobalTensorChart_zero_retention]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
