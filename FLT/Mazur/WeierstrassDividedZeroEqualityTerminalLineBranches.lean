/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleLineBranches

/-!
# Original horizontal branches at the final equality-depth pair

Zero retention and the terminal stage index are reconciled before the two
unit-scaled branch equations are used in descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "G₁" => olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk
local notation "G₂" => olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
/-- Zero retention transport leaves the original first node unchanged. -/
@[reassoc] theorem olderGlobalResidueFirstNode_zero_transport
    (j r : ℕ) (hj : j + 1 ≤ n) (hr : j + 1 + r ≤ n)
    (hk0 : 0 < start + j) (hdepth : 2 * (start + j + 1) ≤ depth) (he : r = 0) :
    olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hdepth ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K hr hj
          (by rw [he, Nat.add_zero])) =
      olderGlobalResidueFirstNode hπ data D j hj 0 hj hk0 hdepth := by
  subst r
  simp only [eqToHom_refl, Category.comp_id]

/-- Zero retention transport leaves the original second node unchanged. -/
@[reassoc] theorem olderGlobalResidueSecondNode_zero_transport
    (j r : ℕ) (hj : j + 1 ≤ n) (hr : j + 1 + r ≤ n)
    (hk0 : 0 < start + j) (hdepth : 2 * (start + j + 1) ≤ depth) (he : r = 0) :
    olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hdepth ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K hr hj
          (by rw [he, Nat.add_zero])) =
      olderGlobalResidueSecondNode hπ data D j hj 0 hj hk0 hdepth := by
  subst r
  simp only [eqToHom_refl, Category.comp_id]

/-- The first terminal attachment keeps its entire signed horizontal branch. -/
@[reassoc] theorem zeroEqualityCycleComponent_terminal_first_lineBranch :
    ProjectiveLine.left K ≫
        (zeroEqualityCycleComponent hπ data D s hs hstart hk hp ⟨s, by omega⟩).left =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleParameterLineBranch c ≫ G₁ := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have H := zeroEqualityCycleComponent_positive_first_lineBranch hπ data D (t + 1) hs
    hstart hk hp ⟨t, by omega⟩
  rw [olderGlobalResidueFirstNode_zero_transport hπ data D
    (t + 1) (t + 1 - (t + 1)) hs _ _ _ (Nat.sub_self _)] at H
  exact H

/-- The second terminal attachment keeps its entire signed horizontal branch. -/
@[reassoc] theorem zeroEqualityCycleComponent_terminal_second_lineBranch :
    ProjectiveLine.right K ≫
        (zeroEqualityCycleComponent hπ data D s hs hstart hk hp ⟨s + 2, by omega⟩).left =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleParameterLineBranch c ≫ G₂ := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have H := zeroEqualityCycleComponent_positive_second_lineBranch hπ data D (t + 1) hs
    hstart hk hp ⟨t, by omega⟩
  rw [olderGlobalResidueSecondNode_zero_transport hπ data D
    (t + 1) (t + 1 - (t + 1)) hs _ _ _ (Nat.sub_self _)] at H
  simpa only [Fin.val_mk, show 2 * (t + 1) + 1 - t = t + 1 + 2 by omega] using H

end FLT.Mazur.WeierstrassDividedDepth
