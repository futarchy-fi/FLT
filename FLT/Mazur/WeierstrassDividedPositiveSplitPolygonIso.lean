/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitPushout
public import FLT.Mazur.PolygonCoconeComparison
import all FLT.Mazur.WeierstrassDividedPositiveSplitPushout

/-!
# Every positive-start strict-depth residue model is the specified polygon

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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveSplitCycleNodes hπ data D s hs hstart hk hp
/-- The actual finite global residue model is the polygon with its proved cyclic incidence. -/
def positiveSplitCyclePolygonIso : PolygonAtlas.polygon K (2 * s + 5) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 5) (by omega) N Q
    (positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison preserves the whole normalization, with its fixed cyclic order. -/
@[reassoc] theorem positiveSplitCyclePolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 5) ≫
      (positiveSplitCyclePolygonIso hπ data D s hs hstart hk hp).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 5) (by omega) N Q
    (positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- Every projective summand is its actual original cyclic component under the comparison. -/
@[reassoc] theorem positiveSplitCyclePolygonIso_component (i : Fin (2 * s + 5)) :
    PolygonPinching.componentι K (2 * s + 5) i ≫
        PolygonAtlas.normalization K (2 * s + 5) ≫
        (positiveSplitCyclePolygonIso hπ data D s hs hstart hk hp).hom = Z i := by
  rw [positiveSplitCyclePolygonIso_normalization, positiveSplitCycleNormalization_ι]

/-- The comparison retains the entire node coproduct. -/
@[reassoc] theorem positiveSplitCyclePolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 5) ≫
      (positiveSplitCyclePolygonIso hπ data D s hs hstart hk hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 5) (by omega) N Q
    (positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- Every polygon node is the original section with its proved cyclic index. -/
@[reassoc] theorem positiveSplitCyclePolygonIso_node (i : Fin (2 * s + 5)) :
    PolygonPinching.nodeι K (2 * s + 5) i ≫ PolygonAtlas.nodes K (2 * s + 5) ≫
        (positiveSplitCyclePolygonIso hπ data D s hs hstart hk hp).hom =
      finalNodeOverSection hπ data D s hs hk hp
        (positiveSplitCycleNodeIndex start s hstart i) := by
  rw [positiveSplitCyclePolygonIso_nodes, positiveSplitCycleNodes_ι]

/-- The same comparison is an isomorphism of the full original underlying schemes. -/
def positiveSplitCyclePolygonSchemeIso : (PolygonAtlas.polygon K (2 * s + 5)).left ≅
    finiteGlobalTensorModel hπ data K (s + 1) hs :=
  (Over.forget _).mapIso (positiveSplitCyclePolygonIso hπ data D s hs hstart hk hp)

end FLT.Mazur.WeierstrassDividedDepth
