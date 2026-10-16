/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopSourcePoleMaps
public import FLT.Mazur.PolygonCompletePointNodeCubicChart
public import FLT.Mazur.PolygonStageNodeParameterUniversalScaling

/-!
# Source-only pole geometry retains the full original input

The source-only localization gives the actual universal scaling and
parameter map. These comparisons need no target-denominator inversion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
local notation "S" => completeIdentityTopSourcePoleFunctions K n h m U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K (m + 1))
local notation "b" => ringMap (stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1))
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K (m + 1))
local notation "p" => (pullback.fst _ _ ≫ Iso.inv (stageNodeParameterIso K (m + 1)) :
  (R) ⟶ chart (Ring K[T;T⁻¹] (m + 1)) (e))
local notation "d" => PolygonInfinitesimal.chart (Ring K (m + 1)) (t) n h (0 : Fin n)
local notation "f" => originalStageToCompatibleProj K n h (m + 1)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)

/-- The source cubic chart retains the actual scaled source followed by the full contraction. -/
@[reassoc] theorem completeIdentityTopSourcePole_cubicChart_inclusion :
    Spec.map (CommRingCat.ofHom (S)) ≫ completePointNodeToCubicChart K n h (m + 1) 0 0 ≫
        integralCurveChart (E) 2 =
      (M) ≫ (V).1.ι ≫ (p) ≫
        Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) ≫ (d) ≫ (f) ≫ (g) := by
  rw [completePointNodeToCubicChart_inclusion]
  simp only [Category.assoc]
  rw [completeIdentityTopSourcePolePatchMap_source_assoc]

/-- The source poles retain the original whole-polygon universal scaling and contraction. -/
@[reassoc] theorem completeIdentityTopSourcePole_universalScaling :
    Spec.map (CommRingCat.ofHom (S)) ≫ completePointNodeToCubicChart K n h (m + 1) 0 0 ≫
        integralCurveChart (E) 2 =
      (M) ≫ (V).1.ι ≫ pullback.fst _ _ ≫
        PolygonInfinitesimal.chart (Ring K (m + 1))[T;T⁻¹] (C (t)) n h (0 : Fin n) ≫
          completeIdentityFiniteScaling K n h (m + 1) ≫ (g) := by
  rw [completeIdentityTopSourcePole_cubicChart_inclusion]
  simp only [Category.assoc, stageNodeParameterIso_inv_universalScaling_assoc]
  simp only [completeIdentityFiniteScaling, Category.assoc,
    PolygonInfinitesimal.chart_universalScaling_assoc]

local notation "Z" => CompleteIdentityTopSourcePolePatch K n h m U
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)

/-- The original ambient smoothing parameter on the unchanged common pole patch. -/
abbrev completeIdentityTopSourcePoleParameter : (Z) :=
  (ι) ((ρ) (completeIdentityTopAmbientParameter K n h m))

/-- The original universal source functions on the same unchanged common pole patch. -/
def completeIdentityTopSourcePoleInputFunctions : ChartRing (C (t)) →+* (Z) :=
  (ι).comp ((ρ).hom.comp ((completeIdentityTopAmbientSourceFunctions K n h m).comp
    (stageNodeParameterMap K (m + 1))))
local notation "F" => completeIdentityTopSourcePoleInputFunctions K n h m U

/-- These functions are exactly the actual original source projection in universal coordinates. -/
@[reassoc] theorem completeIdentityTopSourcePoleInputFunctions_map :
    Spec.map (CommRingCat.ofHom (F)) = (M) ≫ (V).1.ι ≫ pullback.fst _ _ := by
  have he := AffineOpenSpectrumFunctions.map_comp_inclusion (V) (CommRingCat.ofHom (ι))
    (pullback.fst _ _ ≫ (stageNodeParameterIso K (m + 1)).inv)
  have hh := congrArg (fun z ↦ z ≫ (stageNodeParameterIso K (m + 1)).hom) he
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [stageNodeParameterIso_hom, ← Spec.map_comp] at hh
  exact hh.symm

/-- Its smoothing parameter is the original ambient parameter restricted and localized. -/
theorem completeIdentityTopSourcePoleInputFunctions_parameter :
    (F) (algebraMap (Ring K (m + 1))[T;T⁻¹] (ChartRing (C (t))) (C (t))) =
      (ι) ((ρ) (completeIdentityTopAmbientParameter K n h m)) := by
  dsimp only [completeIdentityTopSourcePoleInputFunctions, RingHom.comp_apply]
  rw [stageNodeParameterMap, ringMap_scalar, parameterEval_parameter]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
