/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartClosedPresentation
public import FLT.Mazur.PolygonCompleteIdentityTopChartClosedSplit

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
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "N" => ChartRing (0 : K[T;T⁻¹])
local notation "f" => completeIdentityTopChartClosedAmbientMap K n h m
variable (hm : completeIdentityFiniteMulDefect K n h 0 m = 0)
local notation "r" => completeIdentityTopChartClosedReduction K n h m hm
local notation "J" => completeIdentityTopChartClosedAmbientIdeal K n h m

/-- The original ambient reduction, through the unchanged whole graph chart. -/
def completeIdentityTopAmbientNodeReduction : Γ((R), ⊤) →+* (N) := (r).comp (f)
local notation "d" => completeIdentityTopAmbientNodeReduction K n h m hm

/-- The ambient reduction is surjective onto the full original split node. -/
theorem completeIdentityTopAmbientNodeReduction_surjective : Function.Surjective (d) :=
  (completeIdentityTopChartClosedReduction_surjective K n h m hm).comp
    (completeIdentityTopChartClosedAmbientMap_surjective K n h m)

/-- The entire graph-plus-parameter ideal is killed by the original node reduction. -/
theorem completeIdentityTopChartClosedAmbientIdeal_le_nodeKernel : (J) ≤ RingHom.ker (d) := by
  intro z hz
  change (r) ((f) z) = 0
  rw [(completeIdentityTopChartClosedAmbientMap_eq_zero K n h m z).mpr hz, map_zero]

/-- Original source functions reduce by the original coefficient reduction. -/
theorem completeIdentityTopAmbientNodeReduction_source
    (z : ChartRing (parameter K[T;T⁻¹] (m + 1))) :
    (d) (completeIdentityTopAmbientSourceFunctions K n h m z) =
      topNodeReduction K[T;T⁻¹] m z := by
  change completeIdentityTopChartNodeReduction K n h m hm
    ((completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).appTop
      (completeIdentityTopAmbientSourceFunctions K n h m z)) = _
  rw [completeIdentityTopAmbientSourceFunctions_restrict,
    completeIdentityTopChartNodeReduction_source]

/-- No residual kernel elements are lost by passing from the ambient presentation to the fiber. -/
theorem completeIdentityTopChartResidualKernel_image :
    Ideal.map (f) (RingHom.ker (d)) = RingHom.ker (r) := by
  change Ideal.map (f) (Ideal.comap (f) (RingHom.ker (r))) = _
  exact Ideal.map_comap_of_surjective (f)
    (completeIdentityTopChartClosedAmbientMap_surjective K n h m) _

/-- An ambient representative lies in the residual ideal exactly when its node value vanishes. -/
theorem completeIdentityTopChartResidualKernel_mem (z : Γ((R), ⊤)) :
    (f) z ∈ RingHom.ker (r) ↔ (d) z = 0 := Iff.rfl

/-- Each residual element has a representative in the full original ambient node kernel. -/
theorem completeIdentityTopChartResidualKernel_representative
    (z : completeIdentityTopChartClosedFiber K n h m) (hz : (r) z = 0) :
    ∃ w : Γ((R), ⊤), (d) w = 0 ∧ (f) w = z := by
  obtain ⟨w, rfl⟩ := completeIdentityTopChartClosedAmbientMap_surjective K n h m z
  exact ⟨w, hz, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
