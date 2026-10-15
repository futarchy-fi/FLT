/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSeparatedPullbackGenerators
public import FLT.Mazur.PolygonCompleteIdentityFirstChartAmbientTarget

/-!
# Original source and target functions generate the ambient node relation

Separatedness of the original cubic makes its node relation a closed
subscheme of the product of its two affine node charts. Thus no ambient
functions beyond the original source and target generators are needed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "s" => PolygonInfinitesimal.chart (A)[T;T⁻¹] (C (t)) n h 0
local notation "d" => PolygonInfinitesimal.chart (A) (t) n h 0
local notation "f" => (s) ≫ completeIdentityFiniteInput K n h 0 1 ≫
  completeIdentityActionTarget K n h 0
local notation "g" => (d) ≫ originalStageToCompatibleProj K n h 1 ≫
  completePointToIntegralCubic K n h 0
local notation "w" => WeierstrassIntegralChart.integralCurveStructure
  (completePointWeierstrassCurve K n h 0)
local notation "p" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "q" => completeIdentityFirstAmbientTargetFunctions K n h

/-- The parameter isomorphism retains the entire ambient source-function range. -/
theorem completeIdentityFirstAmbientSourceFunctions_range :
    Set.range (p) = Set.range (pullback.fst (f) (g)).appTop := by
  have hi := (ConcreteCategory.bijective_of_isIso (firstNodeParameterIso K).inv.appTop).surjective
  have hj := (Scheme.ΓSpecIso (.of (ChartRing (e)))).symm.commRingCatIsoToRingEquiv.surjective
  unfold completeIdentityFirstAmbientSourceFunctions
  rw [Scheme.Hom.comp_appTop]
  exact (hi.comp hj).range_comp _

/-- Original target coordinate functions exhaust the second projection's range. -/
theorem completeIdentityFirstAmbientTargetFunctions_range :
    Set.range (q) = Set.range (pullback.snd (f) (g)).appTop := by
  exact (Scheme.ΓSpecIso (.of (ChartRing (t)))).symm.commRingCatIsoToRingEquiv.surjective
    |>.range_comp _

/-- Original source and target functions generate the full ambient ring, with all nilpotents. -/
theorem completeIdentityFirstAmbientFunctions_generate :
    Subring.closure (Set.range (p) ∪ Set.range (q)) = ⊤ := by
  rw [completeIdentityFirstAmbientSourceFunctions_range,
    completeIdentityFirstAmbientTargetFunctions_range]
  let _ : IsAffine (chart (A)[T;T⁻¹] (C (t))) :=
    inferInstanceAs (IsAffine (Spec (.of (ChartRing (C (t))))))
  let _ : IsAffine (chart (A) (t)) :=
    inferInstanceAs (IsAffine (Spec (.of (ChartRing (t)))))
  exact AffineSeparatedPullbackGenerators.closure_eq_top (f) (g) (w)

end FLT.Mazur.PolygonInfinitesimalStages
