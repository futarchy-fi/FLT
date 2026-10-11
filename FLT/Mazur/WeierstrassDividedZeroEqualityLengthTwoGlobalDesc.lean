/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoAtlas
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoAtlas
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoIndexedDesc

/-!
# Global descent on the actual length-two equality fiber

The full four-member atlas glues every compatible cyclic family, retaining
both complete original node maps and uniqueness on the original charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (0 + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ j, ProjectiveLine.zero (ResidueField R) ≫ F j =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) j))
local notation "U" => globalTensorOpenCover hπ data K (0 + 1) hs
local notation "d" => zeroEqualityLengthTwoAtlasFamily hπ data D hs hstart hk hp F w

/-- The cyclic family descends to the entire original length-two residue model. -/
def zeroEqualityLengthTwoGlobalDesc : finiteGlobalTensorModel hπ data K (0 + 1) hs ⟶ Y :=
  (U).glueMorphisms d (zeroEqualityLengthTwoAtlasFamily_compatible hπ data D hs hstart hk hp F w)
local notation "G" => zeroEqualityLengthTwoGlobalDesc hπ data D hs hstart hk hp F w

/-- The global map recovers each of the four complete original atlas maps. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_atlas (i : Fin 4) : m i ≫ G = d i :=
  (U).ι_glueMorphisms d
    (zeroEqualityLengthTwoAtlasFamily_compatible hπ data D hs hstart hk hp F w) i

/-- The entire first node recovers its original full local descent. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_first :
    olderGlobalZeroFirstNode hπ data D 0 hs 0 hs hstart hk ≫ G =
      zeroEqualityLengthTwoFirstDesc data D hs hk hp F w := by
  have H := congrArg (fun q => olderZeroIndexedNodeMap hπ data D 0 hs 0 hs hstart hk 0 ≫ q)
    (zeroEqualityLengthTwoGlobalDesc_atlas hπ data D hs hstart hk hp F w 2)
  have Hnode : olderZeroIndexedNodeMap hπ data D 0 hs 0 hs hstart hk 0 ≫ m 2 =
      olderGlobalZeroFirstNode hπ data D 0 hs 0 hs hstart hk :=
    olderZeroIndexedNodeMap_first_global hπ data D 0 hs 0 hs hstart hk
  rw [← Category.assoc, Hnode] at H
  change _ = _ ≫ zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w at H
  have h := zeroEqualityLengthTwoIndexedDesc_first hπ data D hs hstart hk hp F w
  simp only [eqToHom_refl, Category.id_comp] at h
  exact H.trans h

/-- The opposite original node retains its complete negative parameter descent. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_second :
    olderGlobalZeroSecondNode hπ data D 0 hs 0 hs hstart hk ≫ G =
      zeroEqualityLengthTwoSecondDesc data D hs hk hp F w := by
  have H := congrArg (fun q => olderZeroIndexedNodeMap hπ data D 0 hs 0 hs hstart hk 1 ≫ q)
    (zeroEqualityLengthTwoGlobalDesc_atlas hπ data D hs hstart hk hp F w 2)
  have Hnode : olderZeroIndexedNodeMap hπ data D 0 hs 0 hs hstart hk 1 ≫ m 2 =
      olderGlobalZeroSecondNode hπ data D 0 hs 0 hs hstart hk :=
    olderZeroIndexedNodeMap_second_global hπ data D 0 hs 0 hs hstart hk
  rw [← Category.assoc, Hnode] at H
  change _ = _ ≫ zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w at H
  have h := zeroEqualityLengthTwoIndexedDesc_second hπ data D hs hstart hk hp F w
  simp only [eqToHom_refl, Category.id_comp] at h
  exact H.trans h

/-- Complete restrictions on the original finite atlas determine descent uniquely. -/
theorem zeroEqualityLengthTwoGlobalDesc_unique
    (f : finiteGlobalTensorModel hπ data K (0 + 1) hs ⟶ Y)
    (h : ∀ i, m i ≫ f = d i) : f = G := by
  apply (U).hom_ext
  intro i
  exact (h i).trans (zeroEqualityLengthTwoGlobalDesc_atlas
    hπ data D hs hstart hk hp F w i).symm

end FLT.Mazur.WeierstrassDividedDepth
