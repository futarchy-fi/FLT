/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveConicBranches
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveLineBranches

/-!
# Cyclic components detect maps on every positive-depth retained node

The full original node pushouts give equality of scheme morphisms into arbitrary
schemes. The horizontal branch scalings are cancelled using their inverses.
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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
  (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + (j.val + 1) + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 2 + (s - (j.val + 1)) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega) (by omega) (by omega)

local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Agreement on all cyclic components determines each first positive attachment open. -/
theorem zeroSplitCycleComponent_positive_first_hom_ext :
    G₁ ≫ transport ≫ f = G₁ ≫ transport ≫ g := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · have H := congrArg (fun q => ProjectiveLine.right K ≫ q)
      (h ⟨j.val + 2, by omega⟩)
    simp only [zeroSplitCycleComponent_positive_first_conicBranch_assoc hπ data D s hs
      hstart hk hp ⟨j.val + 1, by omega⟩ (by dsimp; omega)] at H
    exact H
  · have H := congrArg (fun q => ProjectiveLine.left K ≫ q)
      (h ⟨j.val + 1, by omega⟩)
    simp only [zeroSplitCycleComponent_positive_first_lineBranch_assoc] at H
    have H' := congrArg (fun q => ProjectiveLine.chartScaling K tangent ≫ q) H
    simpa only [← Category.assoc, ← ProjectiveLine.chartScaling_mul, mul_inv_cancel,
      ProjectiveLine.chartScaling_one, Category.id_comp] using H'

include h in
/-- The opposite positive attachment is determined with its original negative parameter. -/
theorem zeroSplitCycleComponent_positive_second_hom_ext :
    G₂ ≫ transport ≫ f = G₂ ≫ transport ≫ g := by
  apply (middleNodeBranches_isPushout c hc).hom_ext
  · have H := congrArg (fun q =>
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ q) (h ⟨2 * s + 2 - (j.val + 1), by omega⟩)
    simp only [zeroSplitCycleComponent_positive_second_conicBranch_assoc hπ data D s hs
      hstart hk hp ⟨j.val + 1, by omega⟩ (by dsimp; omega)] at H
    exact H
  · have H := congrArg (fun q => ProjectiveLine.right K ≫ q)
      (h ⟨2 * s + 2 - j.val, by omega⟩)
    simp only [zeroSplitCycleComponent_positive_second_lineBranch_assoc] at H
    have H' := congrArg (fun q => ProjectiveLine.chartScaling K (-tangent) ≫ q) H
    simpa only [← Category.assoc, ← ProjectiveLine.chartScaling_mul, mul_inv_cancel,
      ProjectiveLine.chartScaling_one, Category.id_comp] using H'

end FLT.Mazur.WeierstrassDividedDepth
