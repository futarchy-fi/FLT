/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonAtlas
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCocone

/-!
# The specified polygon maps to the original equality-depth fiber

The proved cyclic cocone gives a canonical comparison from the constructed
polygon. It retains every component and original node in the positive-start
cycle. No universal property of the original finite model is assumed here.
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
  (hstart : 0 < start) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart (by omega) hp
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart (by omega) hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart (by omega)

/-- The actual equality-depth cocone gives a map from the specified polygon over the field. -/
def positiveEqualityCyclePolygonMap : PolygonAtlas.polygon K (2 * s + 4) ⟶ Over.mk p :=
  (PolygonAtlas.isPushout K (2 * s + 4) (by omega)).desc N Q
    (positiveEqualityCycleCocone_condition hπ data D s hs hstart (by omega) hp)

local notation "F" => positiveEqualityCyclePolygonMap hπ data D s hs hstart hp

/-- The comparison retains the full normalization leg with its fixed cyclic order. -/
@[reassoc] theorem positiveEqualityCyclePolygonMap_normalization :
    PolygonAtlas.normalization K (2 * s + 4) ≫ F = N :=
  (PolygonAtlas.isPushout K (2 * s + 4) (by omega)).inl_desc _ _ _

/-- Every projective summand maps to its original whole cyclic component. -/
@[reassoc] theorem positiveEqualityCyclePolygonMap_component (i : Fin (2 * s + 4)) :
    PolygonPinching.componentι K (2 * s + 4) i ≫
        PolygonAtlas.normalization K (2 * s + 4) ≫ F = Z i := by
  rw [positiveEqualityCyclePolygonMap_normalization, positiveEqualityCycleNormalization_ι]

/-- The entire polygon node coproduct keeps the original attachment sections. -/
@[reassoc] theorem positiveEqualityCyclePolygonMap_nodes :
    PolygonAtlas.nodes K (2 * s + 4) ≫ F = Q :=
  (PolygonAtlas.isPushout K (2 * s + 4) (by omega)).inr_desc _ _ _

/-- Each polygon node maps to exactly its original equality-depth attachment. -/
@[reassoc] theorem positiveEqualityCyclePolygonMap_node (i : Fin (2 * s + 4)) :
    PolygonPinching.nodeι K (2 * s + 4) i ≫ PolygonAtlas.nodes K (2 * s + 4) ≫ F =
      equalityNodeOverSection hπ data D s hs (by omega)
        (positiveEqualityCycleNodeIndex start s hstart i) := by
  rw [positiveEqualityCyclePolygonMap_nodes, positiveEqualityCycleNodes_ι]

/-- Every original attachment section is reached, with no collapsed cyclic indices. -/
theorem positiveEqualityCyclePolygonMap_node_sections_injective :
    Function.Injective (fun i : Fin (2 * s + 4) =>
      PolygonPinching.nodeι K (2 * s + 4) i ≫ PolygonAtlas.nodes K (2 * s + 4) ≫ F) := by
  intro i j he
  simp only [positiveEqualityCyclePolygonMap_node] at he
  exact positiveEqualityCycleNodes_sections_injective hπ data D s hs hstart (by omega) he

/-- The original component and node restrictions determine the comparison uniquely. -/
theorem positiveEqualityCyclePolygonMap_unique
    (f : PolygonAtlas.polygon K (2 * s + 4) ⟶ Over.mk p)
    (hf : PolygonAtlas.normalization K (2 * s + 4) ≫ f = N)
    (hq : PolygonAtlas.nodes K (2 * s + 4) ≫ f = Q) : f = F := by
  apply (PolygonAtlas.isPushout K (2 * s + 4) (by omega)).hom_ext
  · exact hf.trans (positiveEqualityCyclePolygonMap_normalization hπ data D s hs hstart hp).symm
  · exact hq.trans (positiveEqualityCyclePolygonMap_nodes hπ data D s hs hstart hp).symm

end FLT.Mazur.WeierstrassDividedDepth
