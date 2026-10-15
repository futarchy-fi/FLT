/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphScheme
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# Individual punctured branches of the original finite graph

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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "L" => (S)[T;T⁻¹]
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "U" => completeIdentityFirstActionUnit K n h i
local notation "V" => completeIdentityFirstActionReciprocalUnit K n h i

/-- Restriction of the entire finite graph algebra to its original left branch. -/
def completeIdentityFirstGraphLeftMap : (E) →ₐ[S] (L) :=
  (AlgHom.fst (S) (L) (L)).comp ((E).restrictScalars (S)).val

/-- Restriction to the original right branch, using its original second coordinate. -/
def completeIdentityFirstGraphRightMap : (E) →ₐ[S] (L) :=
  (AlgHom.snd (S) (L) (L)).comp ((E).restrictScalars (S)).val

/-- Both actual punctured restrictions together detect all graph functions. -/
theorem completeIdentityFirstGraphBranchMaps_ext (z w : E)
    (hl : completeIdentityFirstGraphLeftMap K n h i z =
      completeIdentityFirstGraphLeftMap K n h i w)
    (hr : completeIdentityFirstGraphRightMap K n h i z =
      completeIdentityFirstGraphRightMap K n h i w) : z = w :=
  Subtype.ext (Prod.ext hl hr)

/-- The left source is precisely the unchanged node localization. -/
theorem completeIdentityFirstGraphLeftMap_source :
    (completeIdentityFirstGraphLeftMap K n h i).comp
      (completeIdentityFirstGraphSource K n h i) = leftLaurentMap (e) := rfl

/-- The right source retains the original swapped node coordinate. -/
theorem completeIdentityFirstGraphRightMap_source :
    (completeIdentityFirstGraphRightMap K n h i).comp
      (completeIdentityFirstGraphSource K n h i) =
        (leftLaurentMap (e)).comp (branchSwapMap (e)) := rfl

/-- Every left target function is evaluated by the unchanged original multiplication unit. -/
theorem completeIdentityFirstGraphLeftMap_target :
    (completeIdentityFirstGraphLeftMap K n h i).comp
      (completeIdentityFirstGraphTarget K n h i) =
        (evalUnit (U)).comp (leftLaurentMap (e)) := by
  apply AlgHom.ext
  intro z
  change (completeIdentityFirstActionLaurentEquiv K n h i).toAlgHom _ = _
  rw [completeIdentityFirstActionLaurentEquiv_toAlgHom]
  rfl

/-- Every right target function uses the unchanged original reciprocal multiplication unit. -/
theorem completeIdentityFirstGraphRightMap_target :
    (completeIdentityFirstGraphRightMap K n h i).comp
      (completeIdentityFirstGraphTarget K n h i) =
        (evalUnit (V)).comp ((leftLaurentMap (e)).comp (branchSwapMap (e))) := by
  apply AlgHom.ext
  intro z
  change (completeIdentityFirstActionReciprocalEquiv K n h i).toAlgHom _ = _
  rw [completeIdentityFirstActionReciprocalEquiv_toAlgHom]
  rfl

/-- The original left punctured branch maps into the actual finite graph. -/
def completeIdentityFirstGraphLeftBranch :
    branchTorus (S) ⟶ completeIdentityFirstGraphScheme K n h i :=
  Spec.map (CommRingCat.ofHom (completeIdentityFirstGraphLeftMap K n h i).toRingHom)

/-- The original right punctured branch maps into the same finite graph. -/
def completeIdentityFirstGraphRightBranch :
    branchTorus (S) ⟶ completeIdentityFirstGraphScheme K n h i :=
  Spec.map (CommRingCat.ofHom (completeIdentityFirstGraphRightMap K n h i).toRingHom)

/-- The left branch has exactly the original source-node map. -/
@[reassoc] theorem completeIdentityFirstGraphLeftBranch_source :
    completeIdentityFirstGraphLeftBranch K n h i ≫
      completeIdentityFirstGraphSchemeSource K n h i = leftBranchOpen (S) (e) := by
  rw [completeIdentityFirstGraphLeftBranch, completeIdentityFirstGraphSchemeSource,
    leftBranchOpen_eq_spec, ← Spec.map_comp]
  rfl

/-- The right branch source is the original second punctured coordinate. -/
@[reassoc] theorem completeIdentityFirstGraphRightBranch_source :
    completeIdentityFirstGraphRightBranch K n h i ≫
      completeIdentityFirstGraphSchemeSource K n h i =
        Spec.map (CommRingCat.ofHom
          ((leftLaurentMap (e)).comp (branchSwapMap (e))).toRingHom) := by
  rw [completeIdentityFirstGraphRightBranch, completeIdentityFirstGraphSchemeSource,
    ← Spec.map_comp]
  rfl

/-- The full left target factors through its original punctured target chart. -/
@[reassoc] theorem completeIdentityFirstGraphLeftBranch_target :
    completeIdentityFirstGraphLeftBranch K n h i ≫
      completeIdentityFirstGraphSchemeTarget K n h i =
        Spec.map (CommRingCat.ofHom (evalUnit (U)).toRingHom) ≫
          leftBranchOpen (S) (e) := by
  rw [completeIdentityFirstGraphLeftBranch, completeIdentityFirstGraphSchemeTarget,
    leftBranchOpen_eq_spec, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (completeIdentityFirstGraphLeftMap_target K n h i)))

/-- The full reciprocal target factors through its original second punctured chart. -/
@[reassoc] theorem completeIdentityFirstGraphRightBranch_target :
    completeIdentityFirstGraphRightBranch K n h i ≫
      completeIdentityFirstGraphSchemeTarget K n h i =
        Spec.map (CommRingCat.ofHom (evalUnit (V)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            ((leftLaurentMap (e)).comp (branchSwapMap (e))).toRingHom) := by
  rw [completeIdentityFirstGraphRightBranch, completeIdentityFirstGraphSchemeTarget,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (completeIdentityFirstGraphRightMap_target K n h i)))

end FLT.Mazur.PolygonInfinitesimalStages
