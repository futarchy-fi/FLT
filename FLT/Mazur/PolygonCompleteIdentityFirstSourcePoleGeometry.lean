/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourcePoleMaps
public import FLT.Mazur.PolygonCompletePointNodeCubicChart
public import FLT.Mazur.PolygonFirstNodeParameterUniversalScaling

/-!
# Source-only pole geometry retains the full original input

The source-only localization gives the actual universal scaling and
parameter map. These comparisons need no target-denominator inversion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "b" => ringMap (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1)
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "p" => (pullback.fst _ _ ≫ Iso.inv (firstNodeParameterIso K) :
  (R) ⟶ chart (Ring K[T;T⁻¹] 1) (e))
local notation "d" => PolygonInfinitesimal.chart (Ring K 1) (t) n h (0 : Fin n)
local notation "f" => originalStageToCompatibleProj K n h 1
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)

/-- The source cubic chart retains the actual scaled source followed by the full contraction. -/
@[reassoc] theorem completeIdentityFirstSourcePole_cubicChart_inclusion :
    Spec.map (CommRingCat.ofHom (S)) ≫ completePointNodeToCubicChart K n h 1 0 0 ≫
        integralCurveChart (E) 2 =
      (M) ≫ (V).1.ι ≫ (p) ≫
        Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) ≫ (d) ≫ (f) ≫ (g) := by
  rw [completePointNodeToCubicChart_inclusion]
  simp only [Category.assoc]
  rw [completeIdentityFirstSourcePolePatchMap_source_assoc]

/-- The source poles retain the original whole-polygon universal scaling and contraction. -/
@[reassoc] theorem completeIdentityFirstSourcePole_universalScaling :
    Spec.map (CommRingCat.ofHom (S)) ≫ completePointNodeToCubicChart K n h 1 0 0 ≫
        integralCurveChart (E) 2 =
      (M) ≫ (V).1.ι ≫ pullback.fst _ _ ≫
        PolygonInfinitesimal.chart (Ring K 1)[T;T⁻¹] (C (t)) n h (0 : Fin n) ≫
          completeIdentityFiniteScaling K n h 1 ≫ (g) := by
  rw [completeIdentityFirstSourcePole_cubicChart_inclusion]
  simp only [Category.assoc, firstNodeParameterIso_inv_universalScaling_assoc]
  simp only [completeIdentityFiniteScaling, Category.assoc,
    PolygonInfinitesimal.chart_universalScaling_assoc]

local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)

/-- The original ambient smoothing parameter on the unchanged common pole patch. -/
abbrev completeIdentityFirstSourcePoleParameter : (Z) :=
  (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))

/-- The original universal source functions on the same unchanged common pole patch. -/
def completeIdentityFirstSourcePoleInputFunctions : ChartRing (C (t)) →+* (Z) :=
  (ι).comp ((ρ).hom.comp ((completeIdentityFirstAmbientSourceFunctions K n h).comp
    (firstNodeParameterMap K)))
local notation "F" => completeIdentityFirstSourcePoleInputFunctions K n h U

/-- These functions are exactly the actual original source projection in universal coordinates. -/
@[reassoc] theorem completeIdentityFirstSourcePoleInputFunctions_map :
    Spec.map (CommRingCat.ofHom (F)) = (M) ≫ (V).1.ι ≫ pullback.fst _ _ := by
  have he := AffineOpenSpectrumFunctions.map_comp_inclusion (V) (CommRingCat.ofHom (ι))
    (pullback.fst _ _ ≫ (firstNodeParameterIso K).inv)
  have hh := congrArg (fun z ↦ z ≫ (firstNodeParameterIso K).hom) he
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [firstNodeParameterIso_hom, ← Spec.map_comp] at hh
  exact hh.symm

/-- Its smoothing parameter is the original ambient parameter restricted and localized. -/
theorem completeIdentityFirstSourcePoleInputFunctions_parameter :
    (F) (algebraMap (Ring K 1)[T;T⁻¹] (ChartRing (C (t))) (C (t))) =
      (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h)) := by
  dsimp only [completeIdentityFirstSourcePoleInputFunctions, RingHom.comp_apply]
  rw [firstNodeParameterMap, ringMap_scalar, parameterEval_parameter]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
