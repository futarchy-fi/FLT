/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoIndexedDesc
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoIndexedDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoLocalMaps

/-!
# The full length-two retained tensor map and its conic restriction

Pulling the glued indexed map back to the original tensor chart recovers both
ordered node maps. Their parameter restrictions determine the entire conic map,
with no reduction or separatedness assumption on the target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n) (hstart : start = 0)
  (hk : 2 * (start + 0 + 1) ≤ depth) (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (0 + 1) (Nat.lt_succ_of_le hs))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "V" => olderSuccessiveTensorAtlasIso hπ data K 0 hs 0 hs
local notation "v" => olderGlobalZeroAtlasIso hπ data D 0 hs 0 hs hstart hk
local notation "C" => zeroResidueConicImmersion D (start + 0) (by omega) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "l" => laurentConicComponentConic D (start + 0) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "J" => laurentConicComponentProjectiveIso D (start + 0) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "ρ" => ProjectiveLine.endpointReversal K
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The whole terminal retained tensor chart carries the original indexed descent. -/
def zeroEqualityLengthTwoTensorDesc :
    Spec (.of (ScalarExtension W (π ^ (start + 0)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y :=
  (V).hom ≫ zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w
local notation "d" => zeroEqualityLengthTwoTensorDesc hπ data D hs hstart hk hp F w

/-- The entire normalized fiber recovers its original first full node map. -/
@[reassoc] theorem zeroEqualityLengthTwoTensorDesc_first :
    fullFirstNodeChart a c ha ≫ (v).hom ≫
      zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w =
        zeroEqualityLengthTwoFirstDesc data D hs hk hp F w := by
  simpa only [olderZeroIndexedNodeMap, Fin.cases_zero, eqToHom_refl,
    Category.id_comp, Category.assoc] using
    zeroEqualityLengthTwoIndexedDesc_first hπ data D hs hstart hk hp F w

/-- The opposite full node retains its negative parameter and exterior translation. -/
@[reassoc] theorem zeroEqualityLengthTwoTensorDesc_second :
    fullSecondNodeChart a c ha ≫ (v).hom ≫
      zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w =
        zeroEqualityLengthTwoSecondDesc data D hs hk hp F w := by
  have H := zeroEqualityLengthTwoIndexedDesc_second hπ data D hs hstart hk hp F w
  change (fullSecondNodeChart a c ha ≫ (v).hom) ≫ 𝟙 _ ≫ _ = _ at H
  simpa only [Category.id_comp, Category.assoc] using H

/-- The full original conic has the prescribed reversed terminal restriction. -/
@[reassoc] theorem zeroEqualityLengthTwoTensorDesc_conic :
    C ≫ d = l ≫ (J).inv ≫ ρ ≫ F 1 := by
  change fiberConicImmersion a c ≫ (v).hom ≫
    zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w = _
  apply conicParameter_hom_ext a c ha
  · simp only [Category.assoc]
    rw [← fullNodeFirstBranch_firstChart_assoc, zeroEqualityLengthTwoTensorDesc_first,
      zeroEqualityLengthTwoFirstDesc_conic]
    simp only [equalityTerminalFirstNodeParameter, laurentConicComponentFirstParameter,
      Category.assoc, WeierstrassCurve.map_a₁]
  · simp only [Category.assoc]
    rw [← fullNodeFirstBranch_secondChart_assoc, zeroEqualityLengthTwoTensorDesc_second,
      zeroEqualityLengthTwoSecondDesc_conic]
    simp only [equalityTerminalSecondNodeParameter, laurentConicComponentSecondParameter,
      Category.assoc, WeierstrassCurve.map_a₁]

end FLT.Mazur.WeierstrassDividedDepth
