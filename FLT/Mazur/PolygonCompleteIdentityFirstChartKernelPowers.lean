/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenKernelPower
public import FLT.Mazur.PolygonCompleteIdentityFirstChartPunctureOpens
public import FLT.Mazur.PolygonCompleteIdentityFirstChartBranchQuotient

/-!
# The full comparison kernel is supported at the original source node

Every function in the unchanged comparison kernel is annihilated by powers
of both original source coordinates. This localizes the remaining ideal
at the node without replacing it by its radical or asserting it vanishes.
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
local notation "S" => Ring K[T;T⁻¹] 1
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "l" => completeIdentityFirstLeftToGraphChart K n h
local notation "r" => completeIdentityFirstRightToGraphChart K n h
local notation "f" => SpectrumGlobalRange.ringHom (completeIdentityFirstGraphToChart K n h)
local notation "x" => completeIdentityFirstChartSourceX K n h
local notation "y" => completeIdentityFirstChartSourceY K n h

/-- The full, unreduced comparison kernel in the original chart's global ring. -/
def completeIdentityFirstChartNodeKernel : Ideal Γ((H), ⊤) := RingHom.ker (f)

/-- Every kernel function is killed by a power of the original outgoing source coordinate. -/
theorem completeIdentityFirstChartNodeKernel_x (z : Γ((H), ⊤))
    (hz : z ∈ completeIdentityFirstChartNodeKernel K n h) : ∃ a : ℕ, (x) ^ a * z = 0 := by
  apply AffineOpenKernelPower.exists_pow_mul_eq_zero (l) (x) z
    (le_of_eq (completeIdentityFirstChartSourceX_open K n h))
  have hl := hz
  rw [completeIdentityFirstChartNodeKernel, completeIdentityFirstChartEvaluation_ker] at hl
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (S)[T;T⁻¹])).hom).injective
  change SpectrumGlobalRange.ringHom (l) z = (Scheme.ΓSpecIso _).hom 0
  rw [map_zero]
  exact hl.1

/-- Every kernel function is also killed by a power of the original incoming source coordinate. -/
theorem completeIdentityFirstChartNodeKernel_y (z : Γ((H), ⊤))
    (hz : z ∈ completeIdentityFirstChartNodeKernel K n h) : ∃ b : ℕ, (y) ^ b * z = 0 := by
  apply AffineOpenKernelPower.exists_pow_mul_eq_zero (r) (y) z
    (le_of_eq (completeIdentityFirstChartSourceY_open K n h))
  have hr := hz
  rw [completeIdentityFirstChartNodeKernel, completeIdentityFirstChartEvaluation_ker] at hr
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (S)[T;T⁻¹])).hom).injective
  change SpectrumGlobalRange.ringHom (r) z = (Scheme.ΓSpecIso _).hom 0
  rw [map_zero]
  exact hr.2

/-- Both original coordinate powers annihilate each element of the actual remaining ideal. -/
theorem completeIdentityFirstChartNodeKernel_powers (z : Γ((H), ⊤))
    (hz : z ∈ completeIdentityFirstChartNodeKernel K n h) :
    ∃ a b : ℕ, (x) ^ a * z = 0 ∧ (y) ^ b * z = 0 := by
  obtain ⟨a, ha⟩ := completeIdentityFirstChartNodeKernel_x K n h z hz
  obtain ⟨b, hb⟩ := completeIdentityFirstChartNodeKernel_y K n h z hz
  exact ⟨a, b, ha, hb⟩

end FLT.Mazur.PolygonInfinitesimalStages
