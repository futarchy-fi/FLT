/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicClosed

/-!
# Affine original source-target node lifting spaces

Restrict both coordinates of the original cubic lifting space to their
full original node charts. The source retains the variable Laurent unit;
the target is an original polygon chart. These are affine open subspaces
of the stage lifting space, with the full original cubic relation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i
local notation "d" => chart (A) (t) n h j
local notation "f" => completeIdentityFiniteInput K n h 0 m
local notation "r" => originalStageToCompatibleProj K n h m
local notation "a" => completeIdentityActionTarget K n h 0
local notation "g" => completePointToIntegralCubic K n h 0
local notation "w" => WeierstrassIntegralChart.integralCurveStructure
  (completePointWeierstrassCurve K n h 0)

/-- The original node-pair cubic relation, before taking the graph's closed subscheme. -/
abbrev completeIdentityActionAdicChartSpace : Scheme :=
  pullback ((s) ≫ (f) ≫ (a)) ((d) ≫ (r) ≫ (g))

/-- Its map into the original lifting space retains the two actual chart inclusions. -/
def completeIdentityActionAdicChartSpaceMap :
    completeIdentityActionAdicChartSpace K n h m i j ⟶
      completeIdentityActionAdicLiftSpace K n h m :=
  pullback.map _ _ _ _ (s) (d) (𝟙 _) (by simp) (by simp)

@[reassoc] theorem completeIdentityActionAdicChartSpaceMap_fst :
    completeIdentityActionAdicChartSpaceMap K n h m i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (s) := pullback.lift_fst _ _ _

@[reassoc] theorem completeIdentityActionAdicChartSpaceMap_snd :
    completeIdentityActionAdicChartSpaceMap K n h m i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (d) := pullback.lift_snd _ _ _

/-- Both full original chart restrictions are open; no target-preservation claim is needed. -/
instance completeIdentityActionAdicChartSpaceMap_open :
    IsOpenImmersion (completeIdentityActionAdicChartSpaceMap K n h m i j) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

/-- The original target chart is affine over the separated integral cubic. -/
instance completeIdentityActionAdicTargetChart_affine :
    IsAffineHom ((d) ≫ (r) ≫ (g)) := by
  have : IsAffineHom (((d) ≫ (r) ≫ (g)) ≫ (w)) := by
    rw [Category.assoc, Category.assoc, completePointToIntegralCubic_over,
      originalStageToCompatibleProj_toBase_assoc]
    change IsAffineHom ((d) ≫ toBase (A) (t) n h ≫ baseToSeries K m ≫
      (Spec (.of (PowerSeries K))).toSpecΓ)
    rw [chart_toBase_assoc]
    infer_instance
  exact IsAffineHom.of_comp _ (w)

/-- The unchanged two-node cubic relation is affine, including all nilpotent coefficients. -/
instance completeIdentityActionAdicChartSpace_affine :
    IsAffine (completeIdentityActionAdicChartSpace K n h m i j) := by
  let _ := completeIdentityActionAdicTargetChart_affine K n h m j
  let _ : IsAffine (PolygonSmoothing.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t))) :=
    inferInstanceAs (IsAffine (Spec (.of (PolygonSmoothing.ChartRing (LaurentPolynomial.C (t))))))
  unfold completeIdentityActionAdicChartSpace
  infer_instance

/-- The relation is the equality of the original action and original contraction. -/
@[reassoc] theorem completeIdentityActionAdicChartSpace_cubic :
    pullback.fst ((s) ≫ (f) ≫ (a)) ((d) ≫ (r) ≫ (g)) ≫ (s) ≫ (f) ≫ (a) =
      pullback.snd ((s) ≫ (f) ≫ (a)) ((d) ≫ (r) ≫ (g)) ≫ (d) ≫ (r) ≫ (g) :=
  pullback.condition

end FLT.Mazur.PolygonInfinitesimalStages
