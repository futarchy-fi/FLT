/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartBranchImage
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The exact two-puncture quotient of the literal original chart

Functions on the original chart map onto the full finite graph. Their
kernel is the intersection of the two actual puncture kernels, not its
radical. This is the full branch quotient, with no reduction operation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "E" => completeIdentityFirstErrorAlgebra K n h (0 : Fin n)
local notation "f" => SpectrumGlobalRange.ringHom (completeIdentityFirstGraphToChart K n h)
local notation "l" => SpectrumGlobalRange.ringHom (completeIdentityFirstLeftToGraphChart K n h)
local notation "r" => SpectrumGlobalRange.ringHom (completeIdentityFirstRightToGraphChart K n h)

/-- Cache the finite graph ring before forming its literal quotient presentation. -/
local instance completeIdentityFirstChartBranchQuotientCommRing : CommRing (E) := inferInstance

/-- The comparison evaluates all original chart functions correctly on the outgoing puncture. -/
theorem completeIdentityFirstChartEvaluation_left (z : Γ((H), ⊤)) :
    (l) z = completeIdentityFirstGraphLeftMap K n h 0 ((f) z) := by
  rw [← completeIdentityFirstGraphToChart_left, completeIdentityFirstGraphLeftBranch,
    SpectrumGlobalRange.ringHom_comp_spec]
  rfl

/-- The same comparison retains the actual incoming puncture on every chart function. -/
theorem completeIdentityFirstChartEvaluation_right (z : Γ((H), ⊤)) :
    (r) z = completeIdentityFirstGraphRightMap K n h 0 ((f) z) := by
  rw [← completeIdentityFirstGraphToChart_right, completeIdentityFirstGraphRightBranch,
    SpectrumGlobalRange.ringHom_comp_spec]
  rfl

/-- The exact comparison kernel is the intersection of the two original branch kernels. -/
theorem completeIdentityFirstChartEvaluation_ker :
    RingHom.ker (f) = RingHom.ker (l) ⊓ RingHom.ker (r) := by
  ext z
  change (f) z = 0 ↔ (l) z = 0 ∧ (r) z = 0
  rw [completeIdentityFirstChartEvaluation_left, completeIdentityFirstChartEvaluation_right]
  constructor
  · intro hz
    simp only [hz, map_zero, and_self]
  · rintro ⟨hl, hr⟩
    apply completeIdentityFirstGraphBranchMaps_ext K n h 0
    · simpa only [map_zero] using hl
    · simpa only [map_zero] using hr

/-- The literal two-puncture quotient of the original chart is the full finite graph ring. -/
def completeIdentityFirstChartBranchQuotientEquiv :
    Γ((H), ⊤) ⧸ (RingHom.ker (l) ⊓ RingHom.ker (r)) ≃+* (E) :=
  (Ideal.quotEquivOfEq (completeIdentityFirstChartEvaluation_ker K n h).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (completeIdentityFirstGraphToChart_global_surjective K n h))

/-- The quotient comparison is the original whole-chart comparison on every function. -/
theorem completeIdentityFirstChartBranchQuotientEquiv_mk (z : Γ((H), ⊤)) :
    completeIdentityFirstChartBranchQuotientEquiv K n h (Ideal.Quotient.mk _ z) = (f) z := rfl

end FLT.Mazur.PolygonInfinitesimalStages
