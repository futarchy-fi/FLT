/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorDesc
public import FLT.Mazur.WeierstrassModificationXIncidenceBranchCover
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialNodeDesc
import all FLT.Mazur.WeierstrassModificationXResidueFullNodeGeometry

/-!
# Complete normalized branches of the initial cyclic descent

The two node restrictions determine the whole incidence line and both full conic
parameters. These identities retain the original slope and tangent orientation.
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
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

local notation "E" => residueFiberIso D start hstart (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "d" => positiveEqualityInitialTensorDesc hπ data D s hs hstart hk F w
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)

/-- The first node restriction in full normalized fiber coordinates. -/
@[reassoc] theorem positiveEqualityInitialTensorDesc_first_normalized :
    fullFirstNodeChart a c ha ≫ (E).hom ≫ d =
      positiveEqualityInitialFirstNodeDesc data D s hk F w := by
  simpa only [residueFullFirstNodeChart, Category.assoc] using
    positiveEqualityInitialTensorDesc_first hπ data D s hs hstart hk F w

/-- The second node restriction in full normalized fiber coordinates. -/
@[reassoc] theorem positiveEqualityInitialTensorDesc_second_normalized :
    fullSecondNodeChart a c ha ≫ (E).hom ≫ d =
      positiveEqualityInitialSecondNodeDesc data D s hk F w := by
  simpa only [residueFullSecondNodeChart, Category.assoc] using
    positiveEqualityInitialTensorDesc_second hπ data D s hs hstart hk F w

/-- The full incidence line receives the exterior component map in its original slope. -/
@[reassoc] theorem positiveEqualityInitialTensorDesc_incidence :
    fiberIncidenceImmersion a c ≫ (E).hom ≫ d =
      ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  apply fullNodeIncidenceBranches_hom_ext a c ha
  · rw [← fullNodeSecondBranch_firstChart_assoc a c ha]
    rw [positiveEqualityInitialTensorDesc_first_normalized,
      positiveEqualityInitialFirstNodeDesc_exterior]
  · rw [← fullNodeSecondBranch_secondChart_assoc a c ha]
    rw [positiveEqualityInitialTensorDesc_second_normalized,
      positiveEqualityInitialSecondNodeDesc_exterior]

/-- The first entire normalized conic parameter keeps its prescribed projective chart. -/
@[reassoc] theorem positiveEqualityInitialTensorDesc_first_parameter :
    (conicZeroAffineIso c hc).hom ≫ (conicFirstParameterIso a c ha).inv ≫
      conicFirstOpenImmersion a c ≫ fiberConicImmersion a c ≫ (E).hom ≫ d =
        ProjectiveLine.right K ≫ F 1 := by
  rw [← fullNodeFirstBranch_firstChart_assoc a c ha]
  exact positiveEqualityInitialTensorDesc_first_conic hπ data D s hs hstart hk F w

/-- The opposite normalized parameter uses the last component without changing its sign. -/
@[reassoc] theorem positiveEqualityInitialTensorDesc_second_parameter :
    (conicZeroAffineIso c hc).hom ≫ (conicSecondParameterIso a c ha).inv ≫
      conicSecondOpenImmersion a c ≫ fiberConicImmersion a c ≫ (E).hom ≫ d =
        ProjectiveLine.left K ≫ F ⟨2 * s + 3, by omega⟩ := by
  rw [← fullNodeFirstBranch_secondChart_assoc a c ha]
  exact positiveEqualityInitialTensorDesc_second_conic hπ data D s hs hstart hk F w

end FLT.Mazur.WeierstrassDividedDepth
