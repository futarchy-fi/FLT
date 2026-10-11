/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityPositivePushout
public import FLT.Mazur.PolygonCoconeComparison
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositivePushout

/-!
# The original positive equality-depth start-zero residue model is the specified polygon

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "N" => zeroEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => zeroEqualityCycleNodes hπ data D s hs hk
/-- The actual finite global residue model is the polygon with its proved cyclic incidence. -/
def zeroEqualityPositiveCyclePolygonIso : PolygonAtlas.polygon K (2 * s + 2) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 2) (by omega) N Q
    (zeroEqualityPositiveCycleCocone_isPushout hπ data D s hs hstart hk hp hpos)

/-- The polygon comparison preserves the whole normalization, with its fixed cyclic order. -/
@[reassoc] theorem zeroEqualityPositiveCyclePolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 2) ≫
      (zeroEqualityPositiveCyclePolygonIso hπ data D s hs hstart hk hp hpos).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 2) (by omega) N Q
    (zeroEqualityPositiveCycleCocone_isPushout hπ data D s hs hstart hk hp hpos)

/-- Every projective summand is its actual original cyclic component under the comparison. -/
@[reassoc] theorem zeroEqualityPositiveCyclePolygonIso_component (i : Fin (2 * s + 2)) :
    PolygonPinching.componentι K (2 * s + 2) i ≫
        PolygonAtlas.normalization K (2 * s + 2) ≫
        (zeroEqualityPositiveCyclePolygonIso hπ data D s hs hstart hk hp hpos).hom = Z i := by
  rw [zeroEqualityPositiveCyclePolygonIso_normalization, zeroEqualityCycleNormalization_ι]

/-- The comparison retains the entire node coproduct. -/
@[reassoc] theorem zeroEqualityPositiveCyclePolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 2) ≫
      (zeroEqualityPositiveCyclePolygonIso hπ data D s hs hstart hk hp hpos).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 2) (by omega) N Q
    (zeroEqualityPositiveCycleCocone_isPushout hπ data D s hs hstart hk hp hpos)

/-- Every polygon node is the original section with its proved cyclic index. -/
@[reassoc] theorem zeroEqualityPositiveCyclePolygonIso_node (i : Fin (2 * s + 2)) :
    PolygonPinching.nodeι K (2 * s + 2) i ≫ PolygonAtlas.nodes K (2 * s + 2) ≫
        (zeroEqualityPositiveCyclePolygonIso hπ data D s hs hstart hk hp hpos).hom =
      equalityNodeOverSection hπ data D s hs hk (zeroEqualityCycleNodeIndex start s i) := by
  rw [zeroEqualityPositiveCyclePolygonIso_nodes, zeroEqualityCycleNodes_ι]

/-- The same comparison is an isomorphism of the full original underlying schemes. -/
def zeroEqualityPositiveCyclePolygonSchemeIso : (PolygonAtlas.polygon K (2 * s + 2)).left ≅
    finiteGlobalTensorModel hπ data K (s + 1) hs :=
  (Over.forget _).mapIso (zeroEqualityPositiveCyclePolygonIso hπ data D s hs hstart hk hp hpos)

end FLT.Mazur.WeierstrassDividedDepth
