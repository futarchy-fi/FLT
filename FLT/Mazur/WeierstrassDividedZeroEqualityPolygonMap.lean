/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonAtlas
public import FLT.Mazur.WeierstrassDividedZeroEqualityCocone
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleCoverage

/-!
# The specified polygon maps onto the original equality-depth fiber

The proved cyclic cocone gives a canonical comparison from the constructed
polygon. It retains every component and original node, and is surjective on
points. No universal property of the original finite model is assumed here.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart (by omega) hp
local notation "N" => zeroEqualityCycleNormalization hπ data D s hs hstart (by omega) hp
local notation "Q" => zeroEqualityCycleNodes hπ data D s hs (by omega)

/-- The actual equality-depth cocone gives a map from the specified polygon over the field. -/
def zeroEqualityCyclePolygonMap : PolygonAtlas.polygon K (2 * s + 2) ⟶ Over.mk p :=
  (PolygonAtlas.isPushout K (2 * s + 2) (by omega)).desc N Q
    (zeroEqualityCycleCocone_condition hπ data D s hs hstart (by omega) hp)

local notation "F" => zeroEqualityCyclePolygonMap hπ data D s hs hstart hp

/-- The comparison retains the full normalization leg with its fixed cyclic order. -/
@[reassoc] theorem zeroEqualityCyclePolygonMap_normalization :
    PolygonAtlas.normalization K (2 * s + 2) ≫ F = N :=
  (PolygonAtlas.isPushout K (2 * s + 2) (by omega)).inl_desc _ _ _

/-- Every projective summand maps to its original whole cyclic component. -/
@[reassoc] theorem zeroEqualityCyclePolygonMap_component (i : Fin (2 * s + 2)) :
    PolygonPinching.componentι K (2 * s + 2) i ≫
        PolygonAtlas.normalization K (2 * s + 2) ≫ F = Z i := by
  rw [zeroEqualityCyclePolygonMap_normalization, zeroEqualityCycleNormalization_ι]

/-- The entire polygon node coproduct keeps the original attachment sections. -/
@[reassoc] theorem zeroEqualityCyclePolygonMap_nodes :
    PolygonAtlas.nodes K (2 * s + 2) ≫ F = Q :=
  (PolygonAtlas.isPushout K (2 * s + 2) (by omega)).inr_desc _ _ _

/-- Each polygon node maps to exactly its original equality-depth attachment. -/
@[reassoc] theorem zeroEqualityCyclePolygonMap_node (i : Fin (2 * s + 2)) :
    PolygonPinching.nodeι K (2 * s + 2) i ≫ PolygonAtlas.nodes K (2 * s + 2) ≫ F =
      equalityNodeOverSection hπ data D s hs (by omega)
        (zeroEqualityCycleNodeIndex start s i) := by
  rw [zeroEqualityCyclePolygonMap_nodes, zeroEqualityCycleNodes_ι]

/-- The comparison reaches every point of the original finite residue model. -/
theorem zeroEqualityCyclePolygonMap_surjective : Function.Surjective (F).left := by
  intro z
  obtain ⟨i, x, hx⟩ := zeroEqualityCycleComponent_cover
    hπ data D s hs hstart (by omega) hp z
  refine ⟨(PolygonPinching.componentι K (2 * s + 2) i ≫
    PolygonAtlas.normalization K (2 * s + 2)).left x, ?_⟩
  have he := congrArg Over.Hom.left
    (zeroEqualityCyclePolygonMap_component hπ data D s hs hstart hp i)
  exact (congrArg (fun q => q x) he).trans hx

/-- Every original attachment section is reached, with no collapsed cyclic indices. -/
theorem zeroEqualityCyclePolygonMap_node_sections_injective :
    Function.Injective (fun i : Fin (2 * s + 2) =>
      PolygonPinching.nodeι K (2 * s + 2) i ≫ PolygonAtlas.nodes K (2 * s + 2) ≫ F) := by
  intro i j he
  simp only [zeroEqualityCyclePolygonMap_node] at he
  exact zeroEqualityCycleNodes_sections_injective hπ data D s hs (by omega) he

/-- The original component and node restrictions determine the comparison uniquely. -/
theorem zeroEqualityCyclePolygonMap_unique
    (f : PolygonAtlas.polygon K (2 * s + 2) ⟶ Over.mk p)
    (hf : PolygonAtlas.normalization K (2 * s + 2) ≫ f = N)
    (hq : PolygonAtlas.nodes K (2 * s + 2) ≫ f = Q) : f = F := by
  apply (PolygonAtlas.isPushout K (2 * s + 2) (by omega)).hom_ext
  · exact hf.trans (zeroEqualityCyclePolygonMap_normalization hπ data D s hs hstart hp).symm
  · exact hq.trans (zeroEqualityCyclePolygonMap_nodes hπ data D s hs hstart hp).symm

end FLT.Mazur.WeierstrassDividedDepth
