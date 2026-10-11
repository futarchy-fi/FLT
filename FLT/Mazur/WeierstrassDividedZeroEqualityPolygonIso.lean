/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityPositivePushout
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoPushout
public import FLT.Mazur.PolygonCoconeComparison
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositivePushout

import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoPushout

/-!
# Every equality-depth start-zero residue model is the specified polygon

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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "N" => zeroEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => zeroEqualityCycleNodes hπ data D s hs hk
/-- At every equality depth, including length two, the actual cyclic cocone is a pushout. -/
theorem zeroEqualityCycleCocone_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 2) (by omega))
      (PolygonPinching.toNodes K (2 * s + 2)) N Q := by
  by_cases hz : s = 0
  · subst s
    exact zeroEqualityLengthTwoCocone_isPushout hπ data D hs hstart hk hp
  · exact zeroEqualityPositiveCycleCocone_isPushout hπ data D s hs hstart hk hp (by omega)

/-- The full original equality cocone is also a pushout of underlying schemes. -/
theorem zeroEqualityCycleCocone_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 2) (by omega)).left
      (PolygonPinching.toNodes K (2 * s + 2)).left (N).left (Q).left :=
  (zeroEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp).map (Over.forget _)

/-- The actual finite global residue model is the polygon with its proved cyclic incidence. -/
def zeroEqualityCyclePolygonIso : PolygonAtlas.polygon K (2 * s + 2) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 2) (by omega) N Q
    (zeroEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison preserves the whole normalization, with its fixed cyclic order. -/
@[reassoc] theorem zeroEqualityCyclePolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 2) ≫
      (zeroEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 2) (by omega) N Q
    (zeroEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- Every projective summand is its actual original cyclic component under the comparison. -/
@[reassoc] theorem zeroEqualityCyclePolygonIso_component (i : Fin (2 * s + 2)) :
    PolygonPinching.componentι K (2 * s + 2) i ≫
        PolygonAtlas.normalization K (2 * s + 2) ≫
        (zeroEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom = Z i := by
  rw [zeroEqualityCyclePolygonIso_normalization, zeroEqualityCycleNormalization_ι]

/-- The comparison retains the entire node coproduct. -/
@[reassoc] theorem zeroEqualityCyclePolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 2) ≫
      (zeroEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 2) (by omega) N Q
    (zeroEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- Every polygon node is the original section with its proved cyclic index. -/
@[reassoc] theorem zeroEqualityCyclePolygonIso_node (i : Fin (2 * s + 2)) :
    PolygonPinching.nodeι K (2 * s + 2) i ≫ PolygonAtlas.nodes K (2 * s + 2) ≫
        (zeroEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom =
      equalityNodeOverSection hπ data D s hs hk (zeroEqualityCycleNodeIndex start s i) := by
  rw [zeroEqualityCyclePolygonIso_nodes, zeroEqualityCycleNodes_ι]

/-- The same comparison is an isomorphism of the full original underlying schemes. -/
def zeroEqualityCyclePolygonSchemeIso : (PolygonAtlas.polygon K (2 * s + 2)).left ≅
    finiteGlobalTensorModel hπ data K (s + 1) hs :=
  (Over.forget _).mapIso (zeroEqualityCyclePolygonIso hπ data D s hs hstart hk hp)

end FLT.Mazur.WeierstrassDividedDepth
