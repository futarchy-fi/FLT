/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartPunctureOpens
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicAlgebra
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChartCoordinates
public import FLT.Mazur.PolygonFirstNodeParameterStructure

/-!
# The original first-chart smoothing equation over its flat coefficient map

The product of the actual source coordinates is exactly the original
truncated-base parameter. All scalar comparisons use the unchanged maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
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
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "s" => completeIdentityFirstChartSource K n h
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "a" => completeIdentityActionGraphAdicChartScalars K n h 1 0 0

/-- The parameterized source retains the literal chart's original base structure. -/
@[reassoc] theorem completeIdentityFirstChartSource_structure :
    (s) ≫ chartStructure (S) (e) ≫ Spec.map (CommRingCat.ofHom (c)) =
      completeIdentityActionGraphAdicChartStructure K n h 1 0 0 := by
  rw [completeIdentityFirstChartSource, Category.assoc,
    firstNodeParameterIso_inv_structure,
    completeIdentityActionGraphAdicChartSource_structure]

/-- Every original scalar pulls back through the source node with the same value. -/
theorem completeIdentityFirstChartSource_scalar (r : Ring K 1) :
    (s).appTop ((Scheme.ΓSpecIso (.of (ChartRing (e)))).inv
      (algebraMap (S) (ChartRing (e)) ((c) r))) = (a) r := by
  have he := congrArg Scheme.Hom.appTop
    (completeIdentityFirstChartSource_structure K n h)
  have hn : (Scheme.ΓSpecIso (.of (Ring K 1))).inv ≫
      (Spec.map (CommRingCat.ofHom (c))).appTop ≫
      (chartStructure (S) (e)).appTop =
      CommRingCat.ofHom ((algebraMap (S) (ChartRing (e))).comp (c)) ≫
        (Scheme.ΓSpecIso (.of (ChartRing (e)))).inv := by
    change _ ≫ _ ≫ (Spec.map _).appTop = _
    simp only [← Scheme.Hom.comp_appTop, ← Spec.map_comp,
      Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hh := congrArg (fun f : Γ(Spec (.of (Ring K 1)), ⊤) ⟶ Γ((H), ⊤) ↦
    ((Scheme.ΓSpecIso (.of (Ring K 1))).inv ≫ f) r) he
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hh
  change _ = (a) r at hh
  rw [← Category.assoc] at hh
  rw [hn] at hh
  exact hh

/-- The actual original source coordinates satisfy xy equal to the original base parameter. -/
theorem completeIdentityFirstChartSource_xy :
    completeIdentityFirstChartSourceX K n h * completeIdentityFirstChartSourceY K n h =
      (a) (parameter K 1) := by
  let f : ChartRing (e) →+* Γ((H), ⊤) :=
    (s).appTop.hom.comp (Scheme.ΓSpecIso (.of (ChartRing (e)))).inv.hom
  change f (leftCoordinate (e)) * f (rightCoordinate (e)) = _
  rw [← map_mul, coordinate_relation]
  have he := completeIdentityFirstChartSource_scalar K n h (parameter K 1)
  change f (algebraMap (S) (ChartRing (e)) ((c) (parameter K 1))) = _ at he
  simpa only [stageCoefficientMap_parameter] using he

end FLT.Mazur.PolygonInfinitesimalStages
