/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopBranchOriginal
public import FLT.Mazur.PolygonCompleteIdentityTopGraphScheme
public import FLT.Mazur.PolygonStageNodeParameterEquiv
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Original polygon coordinates on the higher graph

The higher graph has maps into the original source and target node charts.
On its left puncture these are the original finite input and original group
multiplication, and they satisfy the unchanged complete cubic equation.
This does not assert that the equation holds on the entire higher graph.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal LaurentPolynomial LaurentUnitPoints
open PolygonScalingNaturality LaurentStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "q" => Spec.map (CommRingCat.ofHom (coeffMap (parameterEval K (m + 1))))
local notation "b" => Spec.map (CommRingCat.ofHom (coeffMap (c)))
local notation "a" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (evalUnit (completeIdentityTopActionUnit K n h i m))))
local notation "l" => completeIdentityTopGraphLeftBranch K n h i m

/-- The whole higher graph maps to the original variable-parameter source polygon. -/
def completeIdentityTopGraphOriginalSource :
    completeIdentityTopGraphScheme K n h i m ⟶ scalingParameterFamily (A) (t) n h :=
  completeIdentityTopGraphSchemeSource K n h i m ≫ (stageNodeParameterIso K (m + 1)).hom ≫
    PolygonInfinitesimal.chart (A)[T;T⁻¹] (C (t)) n h i

/-- Its target uses the actual original truncated-base projection and original node chart. -/
def completeIdentityTopGraphOriginalTarget :
    completeIdentityTopGraphScheme K n h i m ⟶ (family K (m + 1) n h).left :=
  completeIdentityTopGraphSchemeTarget K n h i m ≫
    Spec.map (CommRingCat.ofHom (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _))) ≫
      PolygonInfinitesimal.chart (A) (t) n h i

/-- On the left puncture the source is exactly the unchanged original finite edge. -/
@[reassoc] theorem completeIdentityTopGraphOriginalSource_left :
    (l) ≫ completeIdentityTopGraphOriginalSource K n h i m =
      (q) ≫ edge (A)[T;T⁻¹] (C (t)) n h i := by
  rw [completeIdentityTopGraphOriginalSource,
    completeIdentityTopGraphLeftBranch_source_assoc, stageNodeParameterIso_hom]
  change leftBranchOpen (S) (e) ≫
    Spec.map (CommRingCat.ofHom (ringMap (parameterEval K (m + 1)) (C (t)) (e) _)) ≫ _ = _
  rw [leftBranchOpen_ringMap_assoc]
  rfl

/-- On the left puncture the target retains the original, unmodified Laurent substitution. -/
@[reassoc] theorem completeIdentityTopGraphOriginalTarget_left :
    (l) ≫ completeIdentityTopGraphOriginalTarget K n h i m =
      (a) ≫ (b) ≫ edge (A) (t) n h i := by
  rw [completeIdentityTopGraphOriginalTarget,
    completeIdentityTopGraphLeftBranch_target_assoc, leftBranchOpen_ringMap_assoc]
  rfl

/-- The original-stage realization of this target is the actual original group product. -/
@[reassoc] theorem completeIdentityTopGraphOriginalTarget_left_realization :
    (l) ≫ completeIdentityTopGraphOriginalTarget K n h i m ≫
        originalStageToCompatibleProj K n h (m + 1) =
      (q) ≫ completeIdentityFiniteOriginalMul K n h i (m + 1) ≫
        (completePointIdentityOpen K n h i).ι := by
  rw [completeIdentityTopGraphOriginalTarget_left_assoc,
    ← completeIdentityStageTorus_inclusion,
    completeIdentityTopActionUnit_originalMul_assoc]

/-- The original cubic source-target equation is proved on this actual punctured branch. -/
@[reassoc] theorem completeIdentityTopGraphOriginalNodes_left_cubic :
    (l) ≫ completeIdentityTopGraphOriginalTarget K n h i m ≫
        originalStageToCompatibleProj K n h (m + 1) ≫ completePointToIntegralCubic K n h i =
      (l) ≫ completeIdentityTopGraphOriginalSource K n h i m ≫
        completeIdentityFiniteInput K n h i (m + 1) ≫ completeIdentityActionTarget K n h i := by
  rw [completeIdentityTopGraphOriginalTarget_left_realization_assoc,
    completeIdentityFiniteOriginalMul_cubic,
    completeIdentityTopGraphOriginalSource_left_assoc]

/-- The left target lands in the original node chart, with no whole-graph range assumption. -/
theorem completeIdentityTopGraphOriginalTarget_left_range :
    Set.range ((l) ≫ completeIdentityTopGraphOriginalTarget K n h i m) ⊆
      Set.range (PolygonInfinitesimal.chart (A) (t) n h i) := by
  rw [completeIdentityTopGraphOriginalTarget_left]
  rintro _ ⟨x, rfl⟩
  exact ⟨((a) ≫ (b) ≫ leftBranchOpen (A) (t)) x, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
