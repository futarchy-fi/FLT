/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialIndexedDesc
public import FLT.Mazur.WeierstrassDividedInitialNodeBranches
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialNodeDesc
import all FLT.Mazur.WeierstrassDividedInitialIndexedNodeCover

/-!
# The entire initial tensor chart carries the strict positive-start descent

The source is the original initial tensor algebra. Both full node restrictions
and their conic parameters survive the fixed atlas transport unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "V" => finiteInitialTensorAtlasIso hπ data K (s + 1) hs
local notation "N₁" => residueFullFirstNodeChart D start hstart (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N₂" => residueFullSecondNodeChart D start hstart (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The complete original initial tensor algebra receives the glued node maps. -/
def positiveSplitInitialTensorDesc :
    Spec (.of (ScalarExtension W (π ^ start)
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y :=
  (V).hom ≫ positiveSplitInitialIndexedDesc hπ data D s hs hstart hk F w
local notation "d" => positiveSplitInitialTensorDesc hπ data D s hs hstart hk F w

/-- Tensor transport preserves the entire first initial node. -/
@[reassoc] theorem positiveSplitInitialTensorDesc_first :
    N₁ ≫ d = positiveSplitInitialFirstNodeDesc data D s hk F w := by
  simpa only [positiveSplitInitialTensorDesc, initialIndexedNodeMap, Fin.cases_zero,
    Category.assoc] using
    positiveSplitInitialIndexedDesc_first hπ data D s hs hstart hk F w

/-- The opposite full initial node retains its translated exterior branch. -/
@[reassoc] theorem positiveSplitInitialTensorDesc_second :
    N₂ ≫ d = positiveSplitInitialSecondNodeDesc data D s hk F w := by
  have H := positiveSplitInitialIndexedDesc_second hπ data D s hs hstart hk F w
  change (N₂ ≫ (V).hom) ≫
    positiveSplitInitialIndexedDesc hπ data D s hs hstart hk F w = _ at H
  simpa only [positiveSplitInitialTensorDesc, Category.assoc] using H

/-- The first complete conic parameter uses the right chart of component one. -/
@[reassoc] theorem positiveSplitInitialTensorDesc_first_conic :
    (conicZeroAffineIso c hc).hom ≫ (fullNodeConicParameterIso a c ha).hom ≫
      fullNodeFirstBranch a c ha ≫ N₁ ≫ d = ProjectiveLine.right K ≫ F 1 := by
  rw [positiveSplitInitialTensorDesc_first, positiveSplitInitialFirstNodeDesc_conic]

/-- The opposite conic parameter keeps the left chart of the final component. -/
@[reassoc] theorem positiveSplitInitialTensorDesc_second_conic :
    (conicZeroAffineIso c hc).hom ≫ (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
      fullNodeFirstBranch (-a) c (ha).neg ≫ N₂ ≫ d =
        ProjectiveLine.left K ≫ F ⟨2 * s + 4, by omega⟩ := by
  rw [positiveSplitInitialTensorDesc_second, positiveSplitInitialSecondNodeDesc_conic]

end FLT.Mazur.WeierstrassDividedDepth
