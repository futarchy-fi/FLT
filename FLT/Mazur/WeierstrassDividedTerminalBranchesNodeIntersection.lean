/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalNodeIncidence
public import FLT.Mazur.PolygonNodeBranchIntersection

/-!
# The actual terminal affine branches meet exactly in the terminal node

Globalization through the original open node chart preserves the full
scheme intersection and both original zero sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "G" => terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "o" => PolygonNodePresentation.aOrigin K

local notation "B₁" => terminalConicFirstBranch hπ data D j hj hk hp
local notation "B₂" => terminalConicSecondBranch hπ data D j hj hk hp
local notation "z" => ProjectiveLine.chartZero K

/-- The entire intersection of the two global terminal affine branches is the base point. -/
theorem terminalConicBranches_isPullback : IsPullback z z B₁ B₂ := by
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ G
    (PolygonNodeBranchIntersection.branches_isPullback K).cone
    (PolygonNodeBranchIntersection.branches_isPullback K).isLimit)

/-- The full branch fiber product is the original residue base scheme. -/
def terminalConicBranchesPullbackIso : Spec (.of K) ≅ pullback B₁ B₂ :=
  (terminalConicBranches_isPullback hπ data D j hj hk hp).isoPullback

/-- The first projection is exactly the original affine origin. -/
@[reassoc] theorem terminalConicBranchesPullbackIso_first :
    (terminalConicBranchesPullbackIso hπ data D j hj hk hp).hom ≫
      pullback.fst B₁ B₂ = z :=
  (terminalConicBranches_isPullback hπ data D j hj hk hp).isoPullback_hom_fst

/-- The second projection keeps the same origin without changing its parameter. -/
@[reassoc] theorem terminalConicBranchesPullbackIso_second :
    (terminalConicBranchesPullbackIso hπ data D j hj hk hp).hom ≫
      pullback.snd B₁ B₂ = z :=
  (terminalConicBranches_isPullback hπ data D j hj hk hp).isoPullback_hom_snd

/-- The full intersection maps to precisely the established actual terminal node section. -/
@[reassoc] theorem terminalConicBranchesPullbackIso_node :
    (terminalConicBranchesPullbackIso hπ data D j hj hk hp).hom ≫
      pullback.fst B₁ B₂ ≫ B₁ = terminalConicNodeSection hπ data D j hj hk hp := by
  rw [terminalConicBranchesPullbackIso_first_assoc, terminalConicFirstBranch_origin]

end FLT.Mazur.WeierstrassDividedDepth
