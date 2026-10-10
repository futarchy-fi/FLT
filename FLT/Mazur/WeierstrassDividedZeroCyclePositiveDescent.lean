/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveConicBranches
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveLineBranches
public import FLT.Mazur.WeierstrassSuccessiveXMiddleScaledDescent

/-!
# Local descent from the actual cyclic components at positive-depth nodes

Adjacent component maps with the prescribed endpoint agreement descend on
both ordered original nodes, keeping the reversed first chain, the negative
opposite conic parameter, and both reciprocal horizontal scales.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Descent with only the original horizontal branch scaled. -/
theorem positiveNode_exists_unique_desc {K : Type u} [Field K] (c : K) (hc : c = 0)
    (a : Kˣ) {Y : Scheme.{u}} (f g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleNodeFirstBranch c hc ≫ d = f ∧
      ProjectiveLine.chartScaling K a ≫ middleNodeSecondBranch c hc ≫ d = g := by
  simpa only [ProjectiveLine.chartScaling_one, Category.id_comp] using
    middleNode_exists_unique_scaled_desc c hc 1 a f g w

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
  (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + (j.val + 1) + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
omit [IsBezout R] in
/-- Maps on the two first-chain components descend on their complete original attachment. -/
theorem zeroSplitCycle_positive_first_exists_unique_desc {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.infinity K ≫ f = ProjectiveLine.zero K ≫ g) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleNodeFirstBranch c hc ≫ d = ProjectiveLine.right K ≫ f ∧
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫ d =
        ProjectiveLine.left K ≫ g := by
  have w' : ProjectiveLine.chartZero K ≫ (ProjectiveLine.right K ≫ f) =
      ProjectiveLine.chartZero K ≫ (ProjectiveLine.left K ≫ g) := by
    simpa only [ProjectiveLine.infinity, ProjectiveLine.zero, Category.assoc] using w
  exact positiveNode_exists_unique_desc c hc (tangent)⁻¹
      (ProjectiveLine.right K ≫ f) (ProjectiveLine.left K ≫ g) w'

omit [IsBezout R] in
/-- Maps on the opposite pair descend with the original negative conic parameter. -/
theorem zeroSplitCycle_positive_second_exists_unique_desc {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.zero K ≫ f = ProjectiveLine.infinity K ≫ g) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleNodeFirstBranch c hc ≫ d =
        Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
          ProjectiveLine.left K ≫ f ∧
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫ d =
        ProjectiveLine.right K ≫ g := by
  rw [middleNode_negativeParameter_eq_scaling]
  have w' : ProjectiveLine.chartZero K ≫
        (ProjectiveLine.chartScaling K (-1) ≫
          ProjectiveLine.left K ≫ f) =
      ProjectiveLine.chartZero K ≫ (ProjectiveLine.right K ≫ g) := by
    rw [ProjectiveLine.chartZero_chartScaling_assoc]
    simpa only [ProjectiveLine.infinity, ProjectiveLine.zero, Category.assoc] using w
  exact positiveNode_exists_unique_desc c hc (-tangent)⁻¹
      (ProjectiveLine.chartScaling K (-1) ≫
        ProjectiveLine.left K ≫ f) (ProjectiveLine.right K ≫ g) w'

end FLT.Mazur.WeierstrassDividedDepth
