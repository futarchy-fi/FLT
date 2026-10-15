/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartClosedPresentation

/-!
# The residual closed-fiber kernel in the original ambient ring

The node reduction is composed with the actual full graph restriction.
Its kernel maps onto the entire residual closed-fiber ideal, and its
quotient by the graph-plus-parameter ideal loses no residual elements.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "N" => ChartRing (0 : K[T;T⁻¹])
local notation "f" => completeIdentityFirstChartClosedAmbientMap K n h
local notation "r" => completeIdentityFirstChartClosedReduction K n h
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h

/-- The original ambient reduction, through the unchanged whole graph chart. -/
def completeIdentityFirstAmbientNodeReduction : Γ((R), ⊤) →+* (N) := (r).comp (f)
local notation "d" => completeIdentityFirstAmbientNodeReduction K n h

/-- The ambient reduction is surjective onto the full original split node. -/
theorem completeIdentityFirstAmbientNodeReduction_surjective : Function.Surjective (d) :=
  (completeIdentityFirstChartClosedReduction_surjective K n h).comp
    (completeIdentityFirstChartClosedAmbientMap_surjective K n h)

/-- The entire graph-plus-parameter ideal is killed by the original node reduction. -/
theorem completeIdentityFirstChartClosedAmbientIdeal_le_nodeKernel : (J) ≤ RingHom.ker (d) := by
  intro z hz
  change (r) ((f) z) = 0
  rw [(completeIdentityFirstChartClosedAmbientMap_eq_zero K n h z).mpr hz, map_zero]

/-- Original source functions reduce by the original coefficient reduction. -/
theorem completeIdentityFirstAmbientNodeReduction_source
    (z : ChartRing (parameter K[T;T⁻¹] 1)) :
    (d) (completeIdentityFirstAmbientSourceFunctions K n h z) =
      firstNodeReduction K[T;T⁻¹] z := by
  change completeIdentityFirstChartNodeReduction K n h
    ((completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).appTop
      (completeIdentityFirstAmbientSourceFunctions K n h z)) = _
  rw [completeIdentityFirstAmbientSourceFunctions_restrict,
    completeIdentityFirstChartNodeReduction_source]

/-- No residual kernel elements are lost by passing from the ambient presentation to the fiber. -/
theorem completeIdentityFirstChartResidualKernel_image :
    Ideal.map (f) (RingHom.ker (d)) = RingHom.ker (r) := by
  change Ideal.map (f) (Ideal.comap (f) (RingHom.ker (r))) = _
  exact Ideal.map_comap_of_surjective (f)
    (completeIdentityFirstChartClosedAmbientMap_surjective K n h) _

/-- An ambient representative lies in the residual ideal exactly when its node value vanishes. -/
theorem completeIdentityFirstChartResidualKernel_mem (z : Γ((R), ⊤)) :
    (f) z ∈ RingHom.ker (r) ↔ (d) z = 0 := Iff.rfl

/-- Each residual element has a representative in the full original ambient node kernel. -/
theorem completeIdentityFirstChartResidualKernel_representative
    (z : completeIdentityFirstChartClosedFiber K n h) (hz : (r) z = 0) :
    ∃ w : Γ((R), ⊤), (d) w = 0 ∧ (f) w = z := by
  obtain ⟨w, rfl⟩ := completeIdentityFirstChartClosedAmbientMap_surjective K n h z
  exact ⟨w, hz, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
