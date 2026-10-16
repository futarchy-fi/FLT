/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartBranchImage
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The exact two-puncture quotient of the literal original chart

Functions on the original chart map onto the full higher graph. Their
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
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "E" => completeIdentityTopGraphAlgebra K n h (0 : Fin n) m
local notation "U" => completeIdentityTopActionUnit K n h 0 m
local notation "V" => completeIdentityTopActionReciprocalUnit K n h 0 m
local notation "f" => SpectrumGlobalRange.ringHom (completeIdentityTopGraphToChart K n h m)
local notation "l" => SpectrumGlobalRange.ringHom (completeIdentityTopLeftToGraphChart K n h m)
local notation "r" => SpectrumGlobalRange.ringHom (completeIdentityTopRightToGraphChart K n h m)

/-- Cache the higher graph ring before forming its literal quotient presentation. -/
local instance completeIdentityTopChartBranchQuotientCommRing : CommRing (E) := inferInstance

/-- The comparison evaluates all original chart functions correctly on the outgoing puncture. -/
theorem completeIdentityTopChartEvaluation_left (z : Γ((H), ⊤)) :
    (l) z = topNodeGraphLeftMap K[T;T⁻¹] m (U) (V) ((f) z) := by
  rw [← completeIdentityTopGraphToChart_left, completeIdentityTopGraphLeftBranch,
    topNodeGraphLeftBranch,
    SpectrumGlobalRange.ringHom_comp_spec]
  rfl

/-- The same comparison retains the actual incoming puncture on every chart function. -/
theorem completeIdentityTopChartEvaluation_right (z : Γ((H), ⊤)) :
    (r) z = topNodeGraphRightMap K[T;T⁻¹] m (U) (V) ((f) z) := by
  rw [← completeIdentityTopGraphToChart_right, completeIdentityTopGraphRightBranch,
    topNodeGraphRightBranch,
    SpectrumGlobalRange.ringHom_comp_spec]
  rfl

/-- The exact comparison kernel is the intersection of the two original branch kernels. -/
theorem completeIdentityTopChartEvaluation_ker :
    RingHom.ker (f) = RingHom.ker (l) ⊓ RingHom.ker (r) := by
  ext z
  change (f) z = 0 ↔ (l) z = 0 ∧ (r) z = 0
  rw [completeIdentityTopChartEvaluation_left, completeIdentityTopChartEvaluation_right]
  constructor
  · intro hz
    simp only [hz, map_zero, and_self]
  · rintro ⟨hl, hr⟩
    apply topNodeGraphBranchMaps_ext K[T;T⁻¹] m (U) (V)
    · simpa only [map_zero] using hl
    · simpa only [map_zero] using hr

/-- The literal two-puncture quotient of the original chart is the full higher graph ring. -/
def completeIdentityTopChartBranchQuotientEquiv :
    Γ((H), ⊤) ⧸ (RingHom.ker (l) ⊓ RingHom.ker (r)) ≃+* (E) :=
  (Ideal.quotEquivOfEq (completeIdentityTopChartEvaluation_ker K n h m).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (completeIdentityTopGraphToChart_global_surjective K n h m))

/-- The quotient comparison is the original whole-chart comparison on every function. -/
theorem completeIdentityTopChartBranchQuotientEquiv_mk (z : Γ((H), ⊤)) :
    completeIdentityTopChartBranchQuotientEquiv K n h m (Ideal.Quotient.mk _ z) = (f) z := rfl

end FLT.Mazur.PolygonInfinitesimalStages
