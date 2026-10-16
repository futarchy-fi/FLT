/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartAmbientSource
public import FLT.Mazur.PolygonCompleteIdentityTopChartClosedLayer
public import FLT.Mazur.SurjectiveParameterQuotient

/-!
# Full ambient presentation of the original higher-chart closed fiber

The ideal is the complete original graph ideal plus the original parameter.
No radical, branch-image quotient, or finite-graph fiber replaces this ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0
local notation "t" => completeIdentityTopAmbientParameter K n h m
local notation "Q" => completeIdentityTopChartClosedFiber K n h m
local notation "q" => completeIdentityTopChartClosedQuotient K n h m

/-- The unchanged full graph ideal together with the original ambient smoothing parameter. -/
def completeIdentityTopChartClosedAmbientIdeal : Ideal Γ((R), ⊤) :=
  completeIdentityActionGraphAdicChartRingIdeal K n h (m + 1) 0 0 ⊔ Ideal.span {(t)}

/-- The actual ambient restriction followed by the literal closed-fiber quotient. -/
def completeIdentityTopChartClosedAmbientMap : Γ((R), ⊤) →+* (Q) :=
  (q).comp (c).appTop.hom
local notation "f" => completeIdentityTopChartClosedAmbientMap K n h m
local notation "J" => completeIdentityTopChartClosedAmbientIdeal K n h m

/-- Every full closed-fiber function has an original ambient representative. -/
theorem completeIdentityTopChartClosedAmbientMap_surjective : Function.Surjective (f) :=
  Ideal.Quotient.mk_surjective.comp
    (completeIdentityActionGraphAdicChart_appTop_surjective K n h (m + 1) 0 0)

/-- The whole kernel is precisely the graph ideal plus the original parameter ideal. -/
theorem completeIdentityTopChartClosedAmbientMap_kernel : RingHom.ker (f) = (J) := by
  have he := SurjectiveParameterQuotient.kernel (c).appTop.hom
    (completeIdentityActionGraphAdicChart_appTop_surjective K n h (m + 1) 0 0) (t)
  rw [completeIdentityTopAmbientParameter_restrict] at he
  exact he

/-- The full original closed fiber presented by its original ambient equations. -/
def completeIdentityTopChartClosedPresentation : Γ((R), ⊤) ⧸ (J) ≃+* (Q) :=
  (Ideal.quotEquivOfEq (completeIdentityTopChartClosedAmbientMap_kernel K n h m).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (completeIdentityTopChartClosedAmbientMap_surjective K n h m))

/-- The presentation retains each original ambient function. -/
theorem completeIdentityTopChartClosedPresentation_mk (z : Γ((R), ⊤)) :
    completeIdentityTopChartClosedPresentation K n h m (Ideal.Quotient.mk _ z) = (f) z := rfl

/-- Vanishing is membership in the full graph-plus-parameter ideal. -/
theorem completeIdentityTopChartClosedAmbientMap_eq_zero (z : Γ((R), ⊤)) :
    (f) z = 0 ↔ z ∈ (J) := by
  change z ∈ RingHom.ker (f) ↔ _
  rw [completeIdentityTopChartClosedAmbientMap_kernel]

/-- This presentation agrees with the existing original graph quotient on every representative. -/
theorem completeIdentityTopChartClosedPresentation_graph (z : Γ((R), ⊤)) :
    completeIdentityTopChartClosedPresentation K n h m (Ideal.Quotient.mk _ z) =
      (q) (completeIdentityActionGraphAdicChartQuotientEquiv K n h (m + 1) 0 0
        (Ideal.Quotient.mk _ z)) := rfl

end FLT.Mazur.PolygonInfinitesimalStages
