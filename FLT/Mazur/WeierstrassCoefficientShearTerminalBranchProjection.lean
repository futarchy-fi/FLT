/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalOverlap
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalBranchCoordinates
public import FLT.Mazur.WeierstrassDividedTensorPointAction

/-!
# Reconstruction and integral projection of both entire terminal branches

Both normalized terminal branches retain the original unsheared tensor and
integral coordinate maps through the actual final divided chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "P" => coefficientShearGluedProjection hπ data S r (j + 1) hj
local notation "F" => finiteDividedGlobalChart hπ data (j + 1) hj

local notation "BFirst" => coefficientShearTerminalFirstBranch
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "TFirst" => tensorShearTerminalFirstMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha
local notation "IFirst" => originalShearTerminalFirstMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha

/-- The complete first branch retains its original tensor-coordinate restriction. -/
@[reassoc] theorem coefficientShearTerminalFirstBranch_tensor :
    BFirst ≫ (G).hom = Spec.map (CommRingCat.ofHom (TFirst).toRingHom) ≫
      globalDividedTensorChart hπ data S (j + 1) hj := by
  rw [coefficientShearTerminalFirstBranch, Category.assoc,
    coefficientShearRootTerminalNode_reconstruction (hp := hp), ← Category.assoc]
  apply congrArg (· ≫ globalDividedTensorChart hπ data S (j + 1) hj)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The complete first branch projects through the original integral divided chart. -/
@[reassoc] theorem coefficientShearTerminalFirstBranch_projection :
    BFirst ≫ P = Spec.map (CommRingCat.ofHom (IFirst).toRingHom) ≫ F := by
  rw [coefficientShearGluedProjection,
    coefficientShearTerminalFirstBranch_tensor_assoc (hp := hp),
    globalDividedTensorChart_integralProjection, ← Category.assoc]
  apply congrArg (· ≫ F)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

local notation "BSecond" => coefficientShearTerminalSecondBranch
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "TSecond" => tensorShearTerminalSecondMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha
local notation "ISecond" => originalShearTerminalSecondMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha

/-- The complete second branch retains its original tensor-coordinate restriction. -/
@[reassoc] theorem coefficientShearTerminalSecondBranch_tensor :
    BSecond ≫ (G).hom = Spec.map (CommRingCat.ofHom (TSecond).toRingHom) ≫
      globalDividedTensorChart hπ data S (j + 1) hj := by
  rw [coefficientShearTerminalSecondBranch, Category.assoc,
    coefficientShearRootTerminalNode_reconstruction (hp := hp), ← Category.assoc]
  apply congrArg (· ≫ globalDividedTensorChart hπ data S (j + 1) hj)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The complete second branch projects through the original integral divided chart. -/
@[reassoc] theorem coefficientShearTerminalSecondBranch_projection :
    BSecond ≫ P = Spec.map (CommRingCat.ofHom (ISecond).toRingHom) ≫ F := by
  rw [coefficientShearGluedProjection,
    coefficientShearTerminalSecondBranch_tensor_assoc (hp := hp),
    globalDividedTensorChart_integralProjection, ← Category.assoc]
  apply congrArg (· ≫ F)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
