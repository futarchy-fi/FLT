/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityPolygonIso
public import FLT.Mazur.PolygonFieldExtension

import all FLT.Mazur.WeierstrassDividedPositiveEqualityPolygonIso

/-!
# Positive-start equality-depth polygons after arbitrary residue-field extension

The actual pulled-back residue model is the specified polygon over the new
field. Its normalization and nodes retain their original coefficient maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
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
variable (L : Type u) [Field L] [Algebra (ResidueField R) L]
local notation "B" => Over.pullback (ProjectiveLineProductCharts.parameterToBase K L)
local notation "N'" => Iso.hom (PolygonFieldExtension.componentsIso K L (2 * s + 4)) ≫
  CategoryTheory.Functor.map B N
local notation "Q'" => Iso.hom (PolygonFieldExtension.nodesIso K L (2 * s + 4)) ≫
  CategoryTheory.Functor.map B Q

/-- The original equality fiber has the specified pinching diagram over every extension field. -/
theorem positiveEqualityFieldCocone_isPushout :
    IsPushout (PolygonPinching.toComponents L (2 * s + 4) (by omega))
      (PolygonPinching.toNodes L (2 * s + 4)) N' Q' :=
  PolygonFieldExtension.isPushout K L (2 * s + 4) (by omega) N Q
    (positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp)

/-- Every residue-field extension of the original model is the polygon over that field. -/
def positiveEqualityFieldPolygonIso :
    PolygonAtlas.polygon L (2 * s + 4) ≅ (B).obj (Over.mk p) :=
  PolygonPinching.polygonIso L (2 * s + 4) (by omega) N' Q'
    (positiveEqualityFieldCocone_isPushout hπ data D s hs hstart hk hp L)

/-- The whole normalization is the original normalization with extended coefficients. -/
@[reassoc] theorem positiveEqualityFieldPolygonIso_normalization :
    PolygonAtlas.normalization L (2 * s + 4) ≫
      (positiveEqualityFieldPolygonIso hπ data D s hs hstart hk hp L).hom = N' :=
  PolygonPinching.normalization_polygonIso L (2 * s + 4) (by omega) N' Q'
    (positiveEqualityFieldCocone_isPushout hπ data D s hs hstart hk hp L)

/-- Every original component retains its projective-line coefficient comparison. -/
@[reassoc] theorem positiveEqualityFieldPolygonIso_component (i : Fin (2 * s + 4)) :
    PolygonPinching.componentι L (2 * s + 4) i ≫
        PolygonAtlas.normalization L (2 * s + 4) ≫
        (positiveEqualityFieldPolygonIso hπ data D s hs hstart hk hp L).hom =
      (ProjectiveLineFieldExtension.componentIso K L).hom ≫ (B).map (Z i) := by
  rw [positiveEqualityFieldPolygonIso_normalization]
  change Sigma.ι _ i ≫ (PolygonFieldExtension.componentsIso K L (2 * s + 4)).hom ≫
    (B).map N = _
  rw [PolygonFieldExtension.componentsIso, PolygonFieldExtension.inclusion_assoc,
    ← Functor.map_comp]
  exact congrArg (fun f => (ProjectiveLineFieldExtension.componentIso K L).hom ≫ (B).map f)
    (positiveEqualityCycleNormalization_ι hπ data D s hs hstart hk hp i)

/-- The entire node coproduct retains its original coefficient extension. -/
@[reassoc] theorem positiveEqualityFieldPolygonIso_nodes :
    PolygonAtlas.nodes L (2 * s + 4) ≫
      (positiveEqualityFieldPolygonIso hπ data D s hs hstart hk hp L).hom = Q' :=
  PolygonPinching.nodes_polygonIso L (2 * s + 4) (by omega) N' Q'
    (positiveEqualityFieldCocone_isPushout hπ data D s hs hstart hk hp L)

/-- Every extended node remains the coefficient extension of its original cyclic section. -/
@[reassoc] theorem positiveEqualityFieldPolygonIso_node (i : Fin (2 * s + 4)) :
    PolygonPinching.nodeι L (2 * s + 4) i ≫ PolygonAtlas.nodes L (2 * s + 4) ≫
        (positiveEqualityFieldPolygonIso hπ data D s hs hstart hk hp L).hom =
      (ProjectiveLineFieldExtension.pointIso K L).hom ≫ (B).map
        (equalityNodeOverSection hπ data D s hs hk
        (positiveEqualityCycleNodeIndex start s hstart i)) := by
  rw [positiveEqualityFieldPolygonIso_nodes]
  change Sigma.ι _ i ≫ (PolygonFieldExtension.nodesIso K L (2 * s + 4)).hom ≫
    (B).map Q = _
  rw [PolygonFieldExtension.nodesIso, PolygonFieldExtension.inclusion_assoc,
    ← Functor.map_comp]
  exact congrArg (fun f => (ProjectiveLineFieldExtension.pointIso K L).hom ≫ (B).map f)
    (positiveEqualityCycleNodes_ι hπ data D s hs hstart hk i)

end FLT.Mazur.WeierstrassDividedDepth
