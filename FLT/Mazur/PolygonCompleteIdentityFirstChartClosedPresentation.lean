/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartAmbientSource
public import FLT.Mazur.PolygonCompleteIdentityFirstChartClosedSplit
public import FLT.Mazur.SurjectiveParameterQuotient

/-!
# Full ambient presentation of the original first-chart closed fiber

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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0
local notation "t" => completeIdentityFirstAmbientParameter K n h
local notation "Q" => completeIdentityFirstChartClosedFiber K n h
local notation "q" => completeIdentityFirstChartClosedQuotient K n h

/-- The unchanged full graph ideal together with the original ambient smoothing parameter. -/
def completeIdentityFirstChartClosedAmbientIdeal : Ideal Γ((R), ⊤) :=
  completeIdentityActionGraphAdicChartRingIdeal K n h 1 0 0 ⊔ Ideal.span {(t)}

/-- The actual ambient restriction followed by the literal closed-fiber quotient. -/
def completeIdentityFirstChartClosedAmbientMap : Γ((R), ⊤) →+* (Q) :=
  (q).comp (c).appTop.hom
local notation "f" => completeIdentityFirstChartClosedAmbientMap K n h
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h

/-- Every full closed-fiber function has an original ambient representative. -/
theorem completeIdentityFirstChartClosedAmbientMap_surjective : Function.Surjective (f) :=
  Ideal.Quotient.mk_surjective.comp
    (completeIdentityActionGraphAdicChart_appTop_surjective K n h 1 0 0)

/-- The whole kernel is precisely the graph ideal plus the original parameter ideal. -/
theorem completeIdentityFirstChartClosedAmbientMap_kernel : RingHom.ker (f) = (J) := by
  have he := SurjectiveParameterQuotient.kernel (c).appTop.hom
    (completeIdentityActionGraphAdicChart_appTop_surjective K n h 1 0 0) (t)
  rw [completeIdentityFirstAmbientParameter_restrict] at he
  exact he

/-- The full original closed fiber presented by its original ambient equations. -/
def completeIdentityFirstChartClosedPresentation : Γ((R), ⊤) ⧸ (J) ≃+* (Q) :=
  (Ideal.quotEquivOfEq (completeIdentityFirstChartClosedAmbientMap_kernel K n h).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (completeIdentityFirstChartClosedAmbientMap_surjective K n h))

/-- The presentation retains each original ambient function. -/
theorem completeIdentityFirstChartClosedPresentation_mk (z : Γ((R), ⊤)) :
    completeIdentityFirstChartClosedPresentation K n h (Ideal.Quotient.mk _ z) = (f) z := rfl

/-- Vanishing is membership in the full graph-plus-parameter ideal. -/
theorem completeIdentityFirstChartClosedAmbientMap_eq_zero (z : Γ((R), ⊤)) :
    (f) z = 0 ↔ z ∈ (J) := by
  change z ∈ RingHom.ker (f) ↔ _
  rw [completeIdentityFirstChartClosedAmbientMap_kernel]

/-- This presentation agrees with the existing original graph quotient on every representative. -/
theorem completeIdentityFirstChartClosedPresentation_graph (z : Γ((R), ⊤)) :
    completeIdentityFirstChartClosedPresentation K n h (Ideal.Quotient.mk _ z) =
      (q) (completeIdentityActionGraphAdicChartQuotientEquiv K n h 1 0 0
        (Ideal.Quotient.mk _ z)) := rfl

end FLT.Mazur.PolygonInfinitesimalStages
