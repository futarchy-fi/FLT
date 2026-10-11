/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoPushout
public import FLT.Mazur.PolygonCoconeComparison
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoPushout

/-!
# The original length-two equality residue model is the specified polygon

The comparison follows from the proved pinching pushout. It preserves all
complete original components and every original cyclic node section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
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
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (0 + 1) hs)
local notation "Z" => zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp
local notation "N" => zeroEqualityCycleNormalization hπ data D 0 hs hstart hk hp
local notation "Q" => zeroEqualityCycleNodes hπ data D 0 hs hk
/-- The actual finite global residue model is the polygon with its proved cyclic incidence. -/
def zeroEqualityLengthTwoPolygonIso : PolygonAtlas.polygon K 2 ≅ Over.mk p :=
  PolygonPinching.polygonIso K 2 (by omega) N Q
    (zeroEqualityLengthTwoCocone_isPushout hπ data D hs hstart hk hp)

/-- The polygon comparison preserves the whole normalization, with its fixed cyclic order. -/
@[reassoc] theorem zeroEqualityLengthTwoPolygonIso_normalization :
    PolygonAtlas.normalization K 2 ≫
      (zeroEqualityLengthTwoPolygonIso hπ data D hs hstart hk hp).hom = N :=
  PolygonPinching.normalization_polygonIso K 2 (by omega) N Q
    (zeroEqualityLengthTwoCocone_isPushout hπ data D hs hstart hk hp)

/-- Every projective summand is its actual original cyclic component under the comparison. -/
@[reassoc] theorem zeroEqualityLengthTwoPolygonIso_component (i : Fin 2) :
    PolygonPinching.componentι K 2 i ≫
        PolygonAtlas.normalization K 2 ≫
        (zeroEqualityLengthTwoPolygonIso hπ data D hs hstart hk hp).hom = Z i := by
  rw [zeroEqualityLengthTwoPolygonIso_normalization,
    zeroEqualityCycleNormalization_ι hπ data D 0 hs hstart hk hp i]

/-- The comparison retains the entire node coproduct. -/
@[reassoc] theorem zeroEqualityLengthTwoPolygonIso_nodes :
    PolygonAtlas.nodes K 2 ≫
      (zeroEqualityLengthTwoPolygonIso hπ data D hs hstart hk hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K 2 (by omega) N Q
    (zeroEqualityLengthTwoCocone_isPushout hπ data D hs hstart hk hp)

/-- Every polygon node is the original section with its proved cyclic index. -/
@[reassoc] theorem zeroEqualityLengthTwoPolygonIso_node (i : Fin 2) :
    PolygonPinching.nodeι K 2 i ≫ PolygonAtlas.nodes K 2 ≫
        (zeroEqualityLengthTwoPolygonIso hπ data D hs hstart hk hp).hom =
      equalityNodeOverSection hπ data D 0 hs hk (zeroEqualityCycleNodeIndex start 0 i) := by
  rw [zeroEqualityLengthTwoPolygonIso_nodes, zeroEqualityCycleNodes_ι hπ data D 0 hs hk i]

/-- The same comparison is an isomorphism of the full original underlying schemes. -/
def zeroEqualityLengthTwoPolygonSchemeIso : (PolygonAtlas.polygon K 2).left ≅
    finiteGlobalTensorModel hπ data K (0 + 1) hs :=
  (Over.forget _).mapIso (zeroEqualityLengthTwoPolygonIso hπ data D hs hstart hk hp)

end FLT.Mazur.WeierstrassDividedDepth
