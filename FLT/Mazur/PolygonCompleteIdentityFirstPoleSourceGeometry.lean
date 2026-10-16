/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchGeometry
public import FLT.Mazur.PolygonCompletePointNodeCubicChart
public import FLT.Mazur.PolygonFirstNodeParameterUniversalScaling

/-!
# The original reciprocal source map on the common pole patch

The source poles come from the unchanged reciprocal substitution followed
by the original complete contraction. This identifies the precise geometric
map that must be compared with the complete cubic action.
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
local notation "M" => completeIdentityFirstPolePatchMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
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

/-- The localized source projection is the original reciprocal substitution on the same patch. -/
@[reassoc] theorem completeIdentityFirstPolePatchMap_source :
    (M) ≫ (V).1.ι ≫ (p) ≫ Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) =
      Spec.map (CommRingCat.ofHom (S)) ≫ Spec.map (CommRingCat.ofHom (η)) := by
  rw [← Category.assoc (V).1.ι, ← Category.assoc (M),
    completeIdentityFirstPolePatchMap, AffineOpenSpectrumFunctions.map_comp_inclusion]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (completeIdentityFirstPoleSourceMap_algebraMap K n h U z).symm

/-- The source cubic chart retains the actual scaled source followed by the full contraction. -/
@[reassoc] theorem completeIdentityFirstPoleSource_cubicChart_inclusion :
    Spec.map (CommRingCat.ofHom (S)) ≫ completePointNodeToCubicChart K n h 1 0 0 ≫
        integralCurveChart (E) 2 =
      (M) ≫ (V).1.ι ≫ (p) ≫
        Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) ≫ (d) ≫ (f) ≫ (g) := by
  rw [completePointNodeToCubicChart_inclusion]
  simp only [Category.assoc]
  rw [completeIdentityFirstPolePatchMap_source_assoc]

/-- The source poles retain the original whole-polygon universal scaling and contraction. -/
@[reassoc] theorem completeIdentityFirstPoleSource_universalScaling :
    Spec.map (CommRingCat.ofHom (S)) ≫ completePointNodeToCubicChart K n h 1 0 0 ≫
        integralCurveChart (E) 2 =
      (M) ≫ (V).1.ι ≫ pullback.fst _ _ ≫
        PolygonInfinitesimal.chart (Ring K 1)[T;T⁻¹] (C (t)) n h (0 : Fin n) ≫
          completeIdentityFiniteScaling K n h 1 ≫ (g) := by
  rw [completeIdentityFirstPoleSource_cubicChart_inclusion]
  simp only [Category.assoc, firstNodeParameterIso_inv_universalScaling_assoc]
  simp only [completeIdentityFiniteScaling, Category.assoc,
    PolygonInfinitesimal.chart_universalScaling_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
