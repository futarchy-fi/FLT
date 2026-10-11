/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityComponentHomExt
public import FLT.Mazur.WeierstrassDividedFinalParameterLineCharts
public import FLT.Mazur.WeierstrassDividedFinalInitialLineCharts
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterDescent

/-!
# Cyclic agreement on every retained horizontal branch

The first retained branches come from the original initial components. Each
later branch comes from its preceding adjacent component. Both signed scales
are cancelled without discarding the complete original node maps.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

variable (j : ℕ) (hj : j ≤ s)
local notation "e" => data (Fin.mk (j + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j + 1 + (s - j) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D j (by omega)
  (s - j) (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D j (by omega)
  (s - j) (by omega) (by omega) (by omega)

include h in
/-- The complete first horizontal branch is determined at every retained depth. -/
theorem positiveEqualityCycleComponent_retained_first_line_hom_ext :
    middleParameterLineBranch c ≫ G₁ ≫ transport ≫ f =
      middleParameterLineBranch c ≫ G₁ ≫ transport ≫ g := by
  cases j with
  | zero =>
    have H := congrArg (fun q => ProjectiveLine.right K ≫ q)
      (positiveEqualityCycleComponent_initial_hom_ext hπ data D s hs hstart hk hp f g h 0)
    simp only [finalInitialComponent_first_right_parameterBranch_assoc] at H
    exact middleNode_cancel_chartScaling (tangent)⁻¹ _ _ H
  | succ j =>
    have H := congrArg (fun q => ProjectiveLine.right K ≫ q)
      (positiveEqualityCycleComponent_adjacent_hom_ext hπ data D s hs hstart hk hp f g h
        ⟨j, by omega⟩ 0)
    simp only [finalAdjacentComponent_first_right_parameterBranch_assoc] at H
    exact middleNode_cancel_chartScaling (tangent)⁻¹ _ _ H

include h in
/-- The complete second horizontal branch is determined at every retained depth. -/
theorem positiveEqualityCycleComponent_retained_second_line_hom_ext :
    middleParameterLineBranch c ≫ G₂ ≫ transport ≫ f =
      middleParameterLineBranch c ≫ G₂ ≫ transport ≫ g := by
  cases j with
  | zero =>
    have H := congrArg (fun q => ProjectiveLine.right K ≫ q)
      (positiveEqualityCycleComponent_initial_hom_ext hπ data D s hs hstart hk hp f g h 1)
    simp only [finalInitialComponent_second_right_parameterBranch_assoc] at H
    exact middleNode_cancel_chartScaling (-tangent)⁻¹ _ _ H
  | succ j =>
    have H := congrArg (fun q => ProjectiveLine.right K ≫ q)
      (positiveEqualityCycleComponent_adjacent_hom_ext hπ data D s hs hstart hk hp f g h
        ⟨j, by omega⟩ 1)
    simp only [finalAdjacentComponent_second_right_parameterBranch_assoc] at H
    exact middleNode_cancel_chartScaling (-tangent)⁻¹ _ _ H

end FLT.Mazur.WeierstrassDividedDepth
