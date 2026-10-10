/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasNodes
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveConicBranches
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveLineBranches
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasNodes
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Component chart restrictions in the original positive cyclic atlas

Each complete affine branch has both its actual global component map and
its prescribed arbitrary-target restriction, including signs and scales.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + (j.val + 1) + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s - j.val + 1) (by omega))
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

/-- The complete first conic branch inside the original fixed atlas object. -/
def zeroSplitCyclePositiveAtlasFirstConic : ProjectiveLine.chart K ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ :=
  middleNodeFirstBranch c hc ≫
    zeroSplitCyclePositiveAtlasFirstNode hπ data D s hs hstart hp j

/-- The complete second conic branch inside the original fixed atlas object. -/
def zeroSplitCyclePositiveAtlasSecondConic : ProjectiveLine.chart K ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ :=
  middleNodeFirstBranch c hc ≫
    zeroSplitCyclePositiveAtlasSecondNode hπ data D s hs hstart hp j

/-- The complete first line branch inside the original fixed atlas object. -/
def zeroSplitCyclePositiveAtlasFirstLine : ProjectiveLine.chart K ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ :=
  ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫
    zeroSplitCyclePositiveAtlasFirstNode hπ data D s hs hstart hp j

/-- The complete second line branch inside the original fixed atlas object. -/
def zeroSplitCyclePositiveAtlasSecondLine : ProjectiveLine.chart K ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ :=
  ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫
    zeroSplitCyclePositiveAtlasSecondNode hπ data D s hs hstart hp j

/-- The first conic branch retains the original cyclic component and parameter. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasFirstConic_global :
    zeroSplitCyclePositiveAtlasFirstConic hπ data D s hs hstart hp j ≫ G =
      ProjectiveLine.right K ≫ (Z ⟨j.val + 2, by omega⟩).left := by
  simp only [zeroSplitCyclePositiveAtlasFirstConic, Category.assoc,
    zeroSplitCyclePositiveAtlasFirstNode_global]
  exact (zeroSplitCycleComponent_positive_first_conicBranch
    hπ data D s hs hstart (by omega) hp ⟨j.val + 1, by omega⟩ (by dsimp; omega)).symm

/-- The second conic branch retains the original cyclic component and parameter. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasSecondConic_global :
    zeroSplitCyclePositiveAtlasSecondConic hπ data D s hs hstart hp j ≫ G =
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ (Z ⟨2 * s + 2 - (j.val + 1), by omega⟩).left := by
  simp only [zeroSplitCyclePositiveAtlasSecondConic, Category.assoc,
    zeroSplitCyclePositiveAtlasSecondNode_global]
  exact (zeroSplitCycleComponent_positive_second_conicBranch
    hπ data D s hs hstart (by omega) hp ⟨j.val + 1, by omega⟩ (by dsimp; omega)).symm

/-- The first line branch retains the original cyclic component and parameter. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasFirstLine_global :
    zeroSplitCyclePositiveAtlasFirstLine hπ data D s hs hstart hp j ≫ G =
      ProjectiveLine.left K ≫ (Z ⟨j.val + 1, by omega⟩).left := by
  simp only [zeroSplitCyclePositiveAtlasFirstLine, Category.assoc,
    zeroSplitCyclePositiveAtlasFirstNode_global]
  exact (zeroSplitCycleComponent_positive_first_lineBranch
    hπ data D s hs hstart (by omega) hp j).symm

/-- The second line branch retains the original cyclic component and parameter. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasSecondLine_global :
    zeroSplitCyclePositiveAtlasSecondLine hπ data D s hs hstart hp j ≫ G =
      ProjectiveLine.right K ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left := by
  simp only [zeroSplitCyclePositiveAtlasSecondLine, Category.assoc,
    zeroSplitCyclePositiveAtlasSecondNode_global]
  exact (zeroSplitCycleComponent_positive_second_lineBranch
    hπ data D s hs hstart (by omega) hp j).symm

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w
  (Fin.mk (s - j.val + 1) (by omega))

/-- The first conic restriction is the prescribed chart of the compatible family. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasFirstConic_desc :
    zeroSplitCyclePositiveAtlasFirstConic hπ data D s hs hstart hp j ≫ d =
      ProjectiveLine.right K ≫ F ⟨j.val + 2, by omega⟩ := by
  simp only [zeroSplitCyclePositiveAtlasFirstConic, Category.assoc,
    zeroSplitCyclePositiveAtlasFirstNode_desc]
  exact zeroSplitCycleFirstLocalDesc_conic data D s hs hstart hp j F w

/-- The second conic restriction is the prescribed chart of the compatible family. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasSecondConic_desc :
    zeroSplitCyclePositiveAtlasSecondConic hπ data D s hs hstart hp j ≫ d =
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ F ⟨2 * s + 2 - (j.val + 1), by omega⟩ := by
  simp only [zeroSplitCyclePositiveAtlasSecondConic, Category.assoc,
    zeroSplitCyclePositiveAtlasSecondNode_desc]
  exact zeroSplitCycleSecondLocalDesc_conic data D s hs hstart hp j F w

/-- The first line restriction is the prescribed chart of the compatible family. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasFirstLine_desc :
    zeroSplitCyclePositiveAtlasFirstLine hπ data D s hs hstart hp j ≫ d =
      ProjectiveLine.left K ≫ F ⟨j.val + 1, by omega⟩ := by
  simp only [zeroSplitCyclePositiveAtlasFirstLine, Category.assoc,
    zeroSplitCyclePositiveAtlasFirstNode_desc]
  exact zeroSplitCycleFirstLocalDesc_line data D s hs hstart hp j F w

/-- The second line restriction is the prescribed chart of the compatible family. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasSecondLine_desc :
    zeroSplitCyclePositiveAtlasSecondLine hπ data D s hs hstart hp j ≫ d =
      ProjectiveLine.right K ≫ F ⟨2 * s + 2 - j.val, by omega⟩ := by
  simp only [zeroSplitCyclePositiveAtlasSecondLine, Category.assoc,
    zeroSplitCyclePositiveAtlasSecondNode_desc]
  exact zeroSplitCycleSecondLocalDesc_line data D s hs hstart hp j F w

end FLT.Mazur.WeierstrassDividedDepth
