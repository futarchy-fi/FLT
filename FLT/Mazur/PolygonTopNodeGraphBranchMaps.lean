/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphScheme
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# Individual punctured branches of the original higher graph

Construct the two branch maps with their original source and target maps.
These equalities hold on every function, including the nilpotent layer.
The target on each branch lies in the same punctured node chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "L" => (S)[T;T⁻¹]
local notation "E" => topNodeGraphAlgebra R m u v
local notation "U" => u
local notation "V" => v

/-- The full original target node maps into its source-target graph. -/
def topNodeGraphTarget : ChartRing (e) →ₐ[S] (E) :=
  ((stageNodeBranchSubstitution R (m + 1) u v).comp
    (stageNodeBranchPair R (m + 1))).codRestrict (E)
      (fun z ↦ (le_sup_right : _ ≤ (E)) ⟨z, rfl⟩)

/-- The graph retains the original target node, before any reduction. -/
def topNodeGraphSchemeTarget :
    topNodeGraphScheme R m u v ⟶ Spec (CommRingCat.of (ChartRing (e))) :=
  Spec.map (CommRingCat.ofHom (topNodeGraphTarget R m u v).toRingHom)

/-- Restriction of the entire higher graph algebra to its original left branch. -/
def topNodeGraphLeftMap : (E) →ₐ[S] (L) :=
  (AlgHom.fst (S) (L) (L)).comp (E).val

/-- Restriction to the original right branch, using its original second coordinate. -/
def topNodeGraphRightMap : (E) →ₐ[S] (L) :=
  (AlgHom.snd (S) (L) (L)).comp (E).val

/-- Both actual punctured restrictions together detect all graph functions. -/
theorem topNodeGraphBranchMaps_ext (z w : E)
    (hl : topNodeGraphLeftMap R m u v z =
      topNodeGraphLeftMap R m u v w)
    (hr : topNodeGraphRightMap R m u v z =
      topNodeGraphRightMap R m u v w) : z = w :=
  Subtype.ext (Prod.ext hl hr)

/-- The left source is precisely the unchanged node localization. -/
theorem topNodeGraphLeftMap_source :
    (topNodeGraphLeftMap R m u v).comp
      (topNodeGraphSource R m u v) = leftLaurentMap (e) := rfl

/-- The right source retains the original swapped node coordinate. -/
theorem topNodeGraphRightMap_source :
    (topNodeGraphRightMap R m u v).comp
      (topNodeGraphSource R m u v) =
        (leftLaurentMap (e)).comp (branchSwapMap (e)) := rfl

/-- Every left target function is evaluated by the unchanged original multiplication unit. -/
theorem topNodeGraphLeftMap_target :
    (topNodeGraphLeftMap R m u v).comp
      (topNodeGraphTarget R m u v) =
        (evalUnit (U)).comp (leftLaurentMap (e)) := rfl

/-- Every right target function uses the unchanged original reciprocal multiplication unit. -/
theorem topNodeGraphRightMap_target :
    (topNodeGraphRightMap R m u v).comp
      (topNodeGraphTarget R m u v) =
        (evalUnit (V)).comp ((leftLaurentMap (e)).comp (branchSwapMap (e))) := rfl

/-- The original left punctured branch maps into the actual higher graph. -/
def topNodeGraphLeftBranch :
    branchTorus (S) ⟶ topNodeGraphScheme R m u v :=
  Spec.map (CommRingCat.ofHom (topNodeGraphLeftMap R m u v).toRingHom)

/-- The original right punctured branch maps into the same higher graph. -/
def topNodeGraphRightBranch :
    branchTorus (S) ⟶ topNodeGraphScheme R m u v :=
  Spec.map (CommRingCat.ofHom (topNodeGraphRightMap R m u v).toRingHom)

/-- The left branch has exactly the original source-node map. -/
@[reassoc] theorem topNodeGraphLeftBranch_source :
    topNodeGraphLeftBranch R m u v ≫
      topNodeGraphSchemeSource R m u v = leftBranchOpen (S) (e) := by
  rw [topNodeGraphLeftBranch, topNodeGraphSchemeSource,
    leftBranchOpen_eq_spec, ← Spec.map_comp]
  rfl

/-- The right branch source is the original second punctured coordinate. -/
@[reassoc] theorem topNodeGraphRightBranch_source :
    topNodeGraphRightBranch R m u v ≫
      topNodeGraphSchemeSource R m u v =
        Spec.map (CommRingCat.ofHom
          ((leftLaurentMap (e)).comp (branchSwapMap (e))).toRingHom) := by
  rw [topNodeGraphRightBranch, topNodeGraphSchemeSource,
    ← Spec.map_comp]
  rfl

/-- The full left target factors through its original punctured target chart. -/
@[reassoc] theorem topNodeGraphLeftBranch_target :
    topNodeGraphLeftBranch R m u v ≫
      topNodeGraphSchemeTarget R m u v =
        Spec.map (CommRingCat.ofHom (evalUnit (U)).toRingHom) ≫
          leftBranchOpen (S) (e) := by
  rw [topNodeGraphLeftBranch, topNodeGraphSchemeTarget,
    leftBranchOpen_eq_spec, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (topNodeGraphLeftMap_target R m u v)))

/-- The full reciprocal target factors through its original second punctured chart. -/
@[reassoc] theorem topNodeGraphRightBranch_target :
    topNodeGraphRightBranch R m u v ≫
      topNodeGraphSchemeTarget R m u v =
        Spec.map (CommRingCat.ofHom (evalUnit (V)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            ((leftLaurentMap (e)).comp (branchSwapMap (e))).toRingHom) := by
  rw [topNodeGraphRightBranch, topNodeGraphSchemeTarget,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (topNodeGraphRightMap_target R m u v)))

end FLT.Mazur.PolygonInfinitesimalStages
