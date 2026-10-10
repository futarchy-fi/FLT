/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePushout
public import FLT.Mazur.PolygonCoconeComparison
import all FLT.Mazur.WeierstrassDividedZeroCyclePushout

/-!
# The original strict-depth start-zero residue model is the specified polygon

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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp
local notation "N" => zeroSplitCycleNormalization hπ data D s hs hstart (by omega) hp
local notation "Q" => zeroSplitCycleNodes hπ data D s hs (by omega) hp
/-- The actual finite global residue model is the polygon with its proved cyclic incidence. -/
def zeroSplitCyclePolygonIso : PolygonAtlas.polygon K (2 * s + 3) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 3) (by omega) N Q
    (zeroSplitCycleCocone_isPushout hπ data D s hs hstart hp)

/-- The polygon comparison preserves the whole normalization, with its fixed cyclic order. -/
@[reassoc] theorem zeroSplitCyclePolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 3) ≫
      (zeroSplitCyclePolygonIso hπ data D s hs hstart hp).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 3) (by omega) N Q
    (zeroSplitCycleCocone_isPushout hπ data D s hs hstart hp)

/-- Every projective summand is its actual original cyclic component under the comparison. -/
@[reassoc] theorem zeroSplitCyclePolygonIso_component (i : Fin (2 * s + 3)) :
    PolygonPinching.componentι K (2 * s + 3) i ≫
        PolygonAtlas.normalization K (2 * s + 3) ≫
        (zeroSplitCyclePolygonIso hπ data D s hs hstart hp).hom = Z i := by
  rw [zeroSplitCyclePolygonIso_normalization, zeroSplitCycleNormalization_ι]

/-- The comparison retains the entire node coproduct. -/
@[reassoc] theorem zeroSplitCyclePolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 3) ≫
      (zeroSplitCyclePolygonIso hπ data D s hs hstart hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 3) (by omega) N Q
    (zeroSplitCycleCocone_isPushout hπ data D s hs hstart hp)

/-- Every polygon node is the original section with its proved cyclic index. -/
@[reassoc] theorem zeroSplitCyclePolygonIso_node (i : Fin (2 * s + 3)) :
    PolygonPinching.nodeι K (2 * s + 3) i ≫ PolygonAtlas.nodes K (2 * s + 3) ≫
        (zeroSplitCyclePolygonIso hπ data D s hs hstart hp).hom =
      finalNodeOverSection hπ data D s hs (by omega) hp (zeroSplitCycleNodeIndex start s i) := by
  rw [zeroSplitCyclePolygonIso_nodes, zeroSplitCycleNodes_ι]

/-- The same comparison is an isomorphism of the full original underlying schemes. -/
def zeroSplitCyclePolygonSchemeIso : (PolygonAtlas.polygon K (2 * s + 3)).left ≅
    finiteGlobalTensorModel hπ data K (s + 1) hs :=
  (Over.forget _).mapIso (zeroSplitCyclePolygonIso hπ data D s hs hstart hp)

end FLT.Mazur.WeierstrassDividedDepth
