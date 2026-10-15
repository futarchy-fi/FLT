/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphToChart
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphRingGenerators
public import FLT.Mazur.SpectrumGlobalRange

/-!
# Closed immersion of the full finite graph into the original adic chart

The comparison retains the entire source node ring and both original target
coordinates. These generate the finite graph, so the comparison is a closed
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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "S" => Ring K[T;T⁻¹] 1
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "E" => completeIdentityFirstErrorAlgebra K n h (0 : Fin n)
local notation "f" => completeIdentityFirstGraphToChart K n h
local notation "s" => completeIdentityFirstGraphSource K n h (0 : Fin n)
local notation "d" => completeIdentityFirstGraphTarget K n h (0 : Fin n)
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "q" => ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _)

/-- Cache the graph ring for the global function map. -/
local instance completeIdentityFirstGraphClosedComparisonCommRing : CommRing (E) := inferInstance

/-- The actual graph-chart functions contain every source-node function. -/
theorem completeIdentityFirstGraphToChart_source_mem (z : ChartRing (e)) :
    (s) z ∈ (SpectrumGlobalRange.ringHom (f)).range := by
  apply SpectrumGlobalRange.factor_mem (f)
    (completeIdentityActionGraphAdicChartSource K n h 1 0 0 ≫
      (firstNodeParameterIso K).inv) (CommRingCat.ofHom (s).toRingHom)
  rw [← Category.assoc, completeIdentityFirstGraphToChart_source, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The actual chart functions contain every unchanged target-node function over the base. -/
theorem completeIdentityFirstGraphToChart_target_mem (z : ChartRing (t)) :
    (d) ((q) z) ∈ (SpectrumGlobalRange.ringHom (f)).range := by
  apply SpectrumGlobalRange.factor_mem (f)
    (completeIdentityActionGraphAdicChartTarget K n h 1 0 0)
    (CommRingCat.ofHom ((d).toRingHom.comp (q)))
  rw [completeIdentityFirstGraphToChart_target, completeIdentityFirstGraphSchemeTarget,
    ← Spec.map_comp]
  rfl

/-- Original source and target coordinates generate the whole finite graph quotient. -/
theorem completeIdentityFirstGraphToChart_global_surjective :
    Function.Surjective (SpectrumGlobalRange.ringHom (f)) := by
  apply completeIdentityFirstGraph_surjective_of_generators K n h 0
  · exact completeIdentityFirstGraphToChart_source_mem K n h
  · simpa only [ringMap_left] using
      completeIdentityFirstGraphToChart_target_mem K n h (leftCoordinate (t))
  · simpa only [ringMap_right] using
      completeIdentityFirstGraphToChart_target_mem K n h (rightCoordinate (t))

/-- The original comparison is a closed immersion, retaining its full nonreduced kernel. -/
instance completeIdentityFirstGraphToChart_closed : IsClosedImmersion (f) :=
  SpectrumGlobalRange.closedImmersion (f)
    (completeIdentityFirstGraphToChart_global_surjective K n h)

end FLT.Mazur.PolygonInfinitesimalStages
