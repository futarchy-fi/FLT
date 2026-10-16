/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopGraphToChart
public import FLT.Mazur.PolygonTopNodeGraphRingGenerators
public import FLT.Mazur.SpectrumGlobalRange

/-!
# Closed immersion of the full higher graph into the original adic chart

The comparison retains the entire source node ring and both original target
coordinates. These generate the higher graph, so the comparison is a closed
immersion with its full kernel. Equality with the adic chart is not assumed.
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
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "E" => completeIdentityTopGraphAlgebra K n h (0 : Fin n) m
local notation "f" => completeIdentityTopGraphToChart K n h m
local notation "U" => completeIdentityTopActionUnit K n h 0 m
local notation "V" => completeIdentityTopActionReciprocalUnit K n h 0 m
local notation "s" => topNodeGraphSource K[T;T⁻¹] m (U) (V)
local notation "d" => topNodeGraphTarget K[T;T⁻¹] m (U) (V)
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "q" => ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _)

/-- Cache the graph ring for the global function map. -/
local instance completeIdentityTopGraphClosedComparisonCommRing : CommRing (E) := inferInstance

/-- The actual graph-chart functions contain every source-node function. -/
theorem completeIdentityTopGraphToChart_source_mem (z : ChartRing (e)) :
    (s) z ∈ (SpectrumGlobalRange.ringHom (f)).range := by
  apply SpectrumGlobalRange.factor_mem (f)
    (completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 ≫
      (stageNodeParameterIso K (m + 1)).inv) (CommRingCat.ofHom (s).toRingHom)
  rw [← Category.assoc, completeIdentityTopGraphToChart_source, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The actual chart functions contain every unchanged target-node function over the base. -/
theorem completeIdentityTopGraphToChart_target_mem (z : ChartRing (t)) :
    (d) ((q) z) ∈ (SpectrumGlobalRange.ringHom (f)).range := by
  apply SpectrumGlobalRange.factor_mem (f)
    (completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0)
    (CommRingCat.ofHom ((d).toRingHom.comp (q)))
  rw [completeIdentityTopGraphToChart_target, completeIdentityTopGraphSchemeTarget,
    topNodeGraphSchemeTarget,
    ← Spec.map_comp]
  rfl

/-- Original source and target coordinates generate the whole higher graph quotient. -/
theorem completeIdentityTopGraphToChart_global_surjective :
    Function.Surjective (SpectrumGlobalRange.ringHom (f)) := by
  apply topNodeGraph_surjective_of_generators K[T;T⁻¹] m (U) (V)
  · exact completeIdentityTopGraphToChart_source_mem K n h m
  · simpa only [ringMap_left] using
      completeIdentityTopGraphToChart_target_mem K n h m (leftCoordinate (t))
  · simpa only [ringMap_right] using
      completeIdentityTopGraphToChart_target_mem K n h m (rightCoordinate (t))

/-- The original comparison is a closed immersion, retaining its full nonreduced kernel. -/
instance completeIdentityTopGraphToChart_closed : IsClosedImmersion (f) :=
  SpectrumGlobalRange.closedImmersion (f)
    (completeIdentityTopGraphToChart_global_surjective K n h m)

end FLT.Mazur.PolygonInfinitesimalStages
