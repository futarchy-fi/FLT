/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityPushout
public import FLT.Mazur.WeierstrassDividedPositiveEqualityPolygonMap
public import FLT.Mazur.PolygonCoconeComparison
import all FLT.Mazur.WeierstrassDividedPositiveEqualityPushout

/-!
# Every positive-start equality-depth residue model is the specified polygon

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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart hk
/-- The actual finite global residue model is the polygon with its proved cyclic incidence. -/
def positiveEqualityCyclePolygonIso : PolygonAtlas.polygon K (2 * s + 4) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 4) (by omega) N Q
    (positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison preserves the whole normalization, with its fixed cyclic order. -/
@[reassoc] theorem positiveEqualityCyclePolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 4) ≫
      (positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 4) (by omega) N Q
    (positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- Every projective summand is its actual original cyclic component under the comparison. -/
@[reassoc] theorem positiveEqualityCyclePolygonIso_component (i : Fin (2 * s + 4)) :
    PolygonPinching.componentι K (2 * s + 4) i ≫
        PolygonAtlas.normalization K (2 * s + 4) ≫
        (positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom = Z i := by
  rw [positiveEqualityCyclePolygonIso_normalization, positiveEqualityCycleNormalization_ι]

/-- The comparison retains the entire node coproduct. -/
@[reassoc] theorem positiveEqualityCyclePolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 4) ≫
      (positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 4) (by omega) N Q
    (positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- Every polygon node is the original section with its proved cyclic index. -/
@[reassoc] theorem positiveEqualityCyclePolygonIso_node (i : Fin (2 * s + 4)) :
    PolygonPinching.nodeι K (2 * s + 4) i ≫ PolygonAtlas.nodes K (2 * s + 4) ≫
        (positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom =
      equalityNodeOverSection hπ data D s hs hk
        (positiveEqualityCycleNodeIndex start s hstart i) := by
  rw [positiveEqualityCyclePolygonIso_nodes, positiveEqualityCycleNodes_ι]

/-- The same comparison is an isomorphism of the full original underlying schemes. -/
def positiveEqualityCyclePolygonSchemeIso : (PolygonAtlas.polygon K (2 * s + 4)).left ≅
    finiteGlobalTensorModel hπ data K (s + 1) hs :=
  (Over.forget _).mapIso (positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp)

/-- The isomorphism is the canonical comparison already defined from the cyclic cocone. -/
theorem positiveEqualityCyclePolygonIso_hom :
    (positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom =
      positiveEqualityCyclePolygonMap hπ data D s hs hstart hp := by
  apply positiveEqualityCyclePolygonMap_unique
  · exact positiveEqualityCyclePolygonIso_normalization hπ data D s hs hstart hk hp
  · exact positiveEqualityCyclePolygonIso_nodes hπ data D s hs hstart hk hp

omit hk in
/-- The canonical surjective polygon comparison is an isomorphism over the residue field. -/
instance positiveEqualityCyclePolygonMap_isIso :
    IsIso (positiveEqualityCyclePolygonMap hπ data D s hs hstart hp) := by
  rw [← positiveEqualityCyclePolygonIso_hom hπ data D s hs hstart hp.le hp]
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
