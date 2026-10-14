/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitPushout
public import FLT.Mazur.NeronPolygonReflection
import all FLT.Mazur.WeierstrassDividedPositiveSplitPushout

/-!
# Reflection of the complete original strict-depth residue model

Descend the reflected normalization through the proved original pinching
pushout. All projective components and original node sections are retained.
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
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveSplitCycleNodes hπ data D s hs hstart hk hp
local notation "H" => positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)

/-- Reflection descended through the actual original residue-model pushout. -/
def positiveSplitReflection : Over.mk p ⟶ Over.mk p :=
  PolygonPinching.polygonReflection K (by omega) N Q H
local notation "σ" => positiveSplitReflection hπ data D s hs hstart hk hp

/-- The full normalization is reflected, with no restriction to its smooth locus. -/
@[reassoc] theorem positiveSplitReflection_normalization :
    N ≫ σ = PolygonPinching.componentsReflection K ≫ N :=
  PolygonPinching.components_polygonReflection K (by omega) N Q H

/-- The entire original node coproduct is retained by reflection. -/
@[reassoc] theorem positiveSplitReflection_nodes :
    Q ≫ σ = PolygonPinching.nodesReflection K ≫ Q :=
  PolygonPinching.nodes_polygonReflection K (by omega) N Q H

/-- Every complete component has index minus i and reversed projective coordinate. -/
@[reassoc] theorem positiveSplitReflection_component (i : Fin (2 * s + 5)) :
    Z i ≫ σ = ρ ≫ Z (PolygonPinching.reflectIndex i) := by
  have h := PolygonPinching.componentι_polygonReflection K (by omega) N Q H i
  simpa only [positiveSplitReflection, positiveSplitCycleNormalization_ι,
    positiveSplitCycleNormalization_ι_assoc] using h

/-- Each actual node has index minus i minus one, including the two initial nodes. -/
@[reassoc] theorem positiveSplitReflection_node (i : Fin (2 * s + 5)) :
    finalNodeOverSection hπ data D s hs hk hp
        (positiveSplitCycleNodeIndex start s hstart i) ≫ σ =
      finalNodeOverSection hπ data D s hs hk hp
        (positiveSplitCycleNodeIndex start s hstart (PolygonPinching.reflectNodeIndex i)) := by
  have h := PolygonPinching.nodeι_polygonReflection K (by omega) N Q H i
  simpa only [positiveSplitReflection, positiveSplitCycleNodes_ι,
    positiveSplitCycleNodes_ι_assoc] using h

/-- Reflection squares to the identity on the whole original model, including its nodes. -/
@[reassoc] theorem positiveSplitReflection_involutive : σ ≫ σ = 𝟙 _ :=
  PolygonPinching.polygonReflection_involutive K (by omega) N Q H

/-- The constructed reflection is an automorphism over the actual residue field. -/
def positiveSplitReflectionIso : Over.mk p ≅ Over.mk p where
  hom := σ
  inv := σ
  hom_inv_id := positiveSplitReflection_involutive hπ data D s hs hstart hk hp
  inv_hom_id := positiveSplitReflection_involutive hπ data D s hs hstart hk hp

/-- The complete component formulas uniquely determine the original-model reflection. -/
theorem positiveSplitReflection_unique (f : Over.mk p ⟶ Over.mk p)
    (h : ∀ i, Z i ≫ f = ρ ≫ Z (PolygonPinching.reflectIndex i)) : f = σ := by
  apply Over.OverMorphism.ext
  apply positiveSplitCycleComponent_hom_ext hπ data D s hs hstart hk hp
  intro i
  exact congrArg Over.Hom.left ((h i).trans
    (positiveSplitReflection_component hπ data D s hs hstart hk hp i).symm)

end FLT.Mazur.WeierstrassDividedDepth
