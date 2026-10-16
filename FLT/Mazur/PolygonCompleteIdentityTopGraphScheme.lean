/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopGraphAlgebra
public import FLT.Mazur.PolygonTopNodeGraphBranchMaps

/-!
# The original higher action as a finite node correspondence

Instantiate the full graph scheme with the unchanged multiplication and
reciprocal units. Both node projections and punctures retain every original
coefficient. Finiteness uses only the preceding original multiplication law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentUnitPoints LaurentStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) (m + 1)
local notation "e" => parameter (R) (m + 1)
local notation "U" => completeIdentityTopActionUnit K n h i m
local notation "V" => completeIdentityTopActionReciprocalUnit K n h i m

/-- The entire original higher source-target graph, with its full scheme structure. -/
def completeIdentityTopGraphScheme : Scheme := topNodeGraphScheme (R) m (U) (V)

/-- The unchanged source-node projection. -/
def completeIdentityTopGraphSchemeSource :
    completeIdentityTopGraphScheme K n h i m ⟶ chart (S) (e) :=
  topNodeGraphSchemeSource (R) m (U) (V)

/-- The unchanged original-action target-node projection. -/
def completeIdentityTopGraphSchemeTarget :
    completeIdentityTopGraphScheme K n h i m ⟶ chart (S) (e) :=
  topNodeGraphSchemeTarget (R) m (U) (V)

/-- The original left puncture of the higher graph. -/
def completeIdentityTopGraphLeftBranch :
    branchTorus (S) ⟶ completeIdentityTopGraphScheme K n h i m :=
  topNodeGraphLeftBranch (R) m (U) (V)

/-- The original right puncture of the same higher graph. -/
def completeIdentityTopGraphRightBranch :
    branchTorus (S) ⟶ completeIdentityTopGraphScheme K n h i m :=
  topNodeGraphRightBranch (R) m (U) (V)

/-- The full left source is the original punctured node map. -/
@[reassoc] theorem completeIdentityTopGraphLeftBranch_source :
    completeIdentityTopGraphLeftBranch K n h i m ≫
      completeIdentityTopGraphSchemeSource K n h i m = leftBranchOpen (S) (e) :=
  topNodeGraphLeftBranch_source (R) m (U) (V)

/-- The full right source is the original swapped node map. -/
@[reassoc] theorem completeIdentityTopGraphRightBranch_source :
    completeIdentityTopGraphRightBranch K n h i m ≫
      completeIdentityTopGraphSchemeSource K n h i m =
        Spec.map (CommRingCat.ofHom
          ((leftLaurentMap (e)).comp (branchSwapMap (e))).toRingHom) :=
  topNodeGraphRightBranch_source (R) m (U) (V)

/-- The full left target is exactly original multiplication on the puncture. -/
@[reassoc] theorem completeIdentityTopGraphLeftBranch_target :
    completeIdentityTopGraphLeftBranch K n h i m ≫
      completeIdentityTopGraphSchemeTarget K n h i m =
        Spec.map (CommRingCat.ofHom (evalUnit (U)).toRingHom) ≫ leftBranchOpen (S) (e) :=
  topNodeGraphLeftBranch_target (R) m (U) (V)

/-- The full right target is the original reciprocal multiplication. -/
@[reassoc] theorem completeIdentityTopGraphRightBranch_target :
    completeIdentityTopGraphRightBranch K n h i m ≫
      completeIdentityTopGraphSchemeTarget K n h i m =
        Spec.map (CommRingCat.ofHom (evalUnit (V)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            ((leftLaurentMap (e)).comp (branchSwapMap (e))).toRingHom) :=
  topNodeGraphRightBranch_target (R) m (U) (V)

/-- The preceding original law proves finiteness over the unchanged source node. -/
theorem completeIdentityTopGraphSchemeSource_finite
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) :
    IsFinite (completeIdentityTopGraphSchemeSource K n h i m) :=
  topNodeGraphSchemeSource_finite (R) m (U) (V) (parameterUnit K (m + 1))
    (completeIdentityTopActionUnit_restriction K n h i m hm)
    (completeIdentityTopActionReciprocalUnit_restriction K n h i m hm)

end FLT.Mazur.PolygonInfinitesimalStages
