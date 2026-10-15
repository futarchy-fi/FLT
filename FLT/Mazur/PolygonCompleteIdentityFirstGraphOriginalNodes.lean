/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstBranchOriginal
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphBranchMaps
public import FLT.Mazur.PolygonFirstNodeParameterEquiv
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Original polygon coordinates on the finite first graph

The finite graph has maps into the original source and target node charts.
On its left puncture these are the original finite input and original group
multiplication, and they satisfy the unchanged complete cubic equation.
This does not assert that the equation holds on the entire finite graph.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal LaurentPolynomial LaurentUnitPoints
open PolygonScalingNaturality LaurentFirstStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "A" => Ring K 1
local notation "S" => Ring K[T;T⁻¹] 1
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "q" => Spec.map (CommRingCat.ofHom (coeffMap (parameterEval K)))
local notation "b" => Spec.map (CommRingCat.ofHom (coeffMap (c)))
local notation "a" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (evalUnit (completeIdentityFirstActionUnit K n h i))))
local notation "l" => completeIdentityFirstGraphLeftBranch K n h i

/-- The whole finite graph maps to the original variable-parameter source polygon. -/
def completeIdentityFirstGraphOriginalSource :
    completeIdentityFirstGraphScheme K n h i ⟶ scalingParameterFamily (A) (t) n h :=
  completeIdentityFirstGraphSchemeSource K n h i ≫ (firstNodeParameterIso K).hom ≫
    PolygonInfinitesimal.chart (A)[T;T⁻¹] (C (t)) n h i

/-- Its target uses the actual original truncated-base projection and original node chart. -/
def completeIdentityFirstGraphOriginalTarget :
    completeIdentityFirstGraphScheme K n h i ⟶ (family K 1 n h).left :=
  completeIdentityFirstGraphSchemeTarget K n h i ≫
    Spec.map (CommRingCat.ofHom (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _))) ≫
      PolygonInfinitesimal.chart (A) (t) n h i

/-- On the left puncture the source is exactly the unchanged original finite edge. -/
@[reassoc] theorem completeIdentityFirstGraphOriginalSource_left :
    (l) ≫ completeIdentityFirstGraphOriginalSource K n h i =
      (q) ≫ edge (A)[T;T⁻¹] (C (t)) n h i := by
  rw [completeIdentityFirstGraphOriginalSource,
    completeIdentityFirstGraphLeftBranch_source_assoc, firstNodeParameterIso_hom]
  change leftBranchOpen (S) (e) ≫
    Spec.map (CommRingCat.ofHom (ringMap (parameterEval K) (C (t)) (e) _)) ≫ _ = _
  rw [leftBranchOpen_ringMap_assoc]
  rfl

/-- On the left puncture the target retains the original, unmodified Laurent substitution. -/
@[reassoc] theorem completeIdentityFirstGraphOriginalTarget_left :
    (l) ≫ completeIdentityFirstGraphOriginalTarget K n h i =
      (a) ≫ (b) ≫ edge (A) (t) n h i := by
  rw [completeIdentityFirstGraphOriginalTarget,
    completeIdentityFirstGraphLeftBranch_target_assoc, leftBranchOpen_ringMap_assoc]
  rfl

/-- The original-stage realization of this target is the actual original group product. -/
@[reassoc] theorem completeIdentityFirstGraphOriginalTarget_left_realization :
    (l) ≫ completeIdentityFirstGraphOriginalTarget K n h i ≫
        originalStageToCompatibleProj K n h 1 =
      (q) ≫ completeIdentityFiniteOriginalMul K n h i 1 ≫
        (completePointIdentityOpen K n h i).ι := by
  rw [completeIdentityFirstGraphOriginalTarget_left_assoc,
    ← completeIdentityStageTorus_inclusion,
    completeIdentityFirstActionUnit_originalMul_assoc]

/-- The original cubic source-target equation is proved on this actual punctured branch. -/
@[reassoc] theorem completeIdentityFirstGraphOriginalNodes_left_cubic :
    (l) ≫ completeIdentityFirstGraphOriginalTarget K n h i ≫
        originalStageToCompatibleProj K n h 1 ≫ completePointToIntegralCubic K n h i =
      (l) ≫ completeIdentityFirstGraphOriginalSource K n h i ≫
        completeIdentityFiniteInput K n h i 1 ≫ completeIdentityActionTarget K n h i := by
  rw [completeIdentityFirstGraphOriginalTarget_left_realization_assoc,
    completeIdentityFiniteOriginalMul_cubic,
    completeIdentityFirstGraphOriginalSource_left_assoc]

/-- The left target lands in the original node chart, with no whole-graph range assumption. -/
theorem completeIdentityFirstGraphOriginalTarget_left_range :
    Set.range ((l) ≫ completeIdentityFirstGraphOriginalTarget K n h i) ⊆
      Set.range (PolygonInfinitesimal.chart (A) (t) n h i) := by
  rw [completeIdentityFirstGraphOriginalTarget_left]
  rintro _ ⟨x, rfl⟩
  exact ⟨((a) ≫ (b) ≫ leftBranchOpen (A) (t)) x, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
