/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenKernelPower
public import FLT.Mazur.PolygonCompleteIdentityTopChartPunctureOpens
public import FLT.Mazur.PolygonCompleteIdentityTopChartBranchQuotient

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
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "l" => completeIdentityTopLeftToGraphChart K n h m
local notation "r" => completeIdentityTopRightToGraphChart K n h m
local notation "f" => SpectrumGlobalRange.ringHom (completeIdentityTopGraphToChart K n h m)
local notation "x" => completeIdentityTopChartSourceX K n h m
local notation "y" => completeIdentityTopChartSourceY K n h m

/-- The full, unreduced comparison kernel in the original chart's global ring. -/
def completeIdentityTopChartNodeKernel : Ideal Γ((H), ⊤) := RingHom.ker (f)

/-- Every kernel function is killed by a power of the original outgoing source coordinate. -/
theorem completeIdentityTopChartNodeKernel_x (z : Γ((H), ⊤))
    (hz : z ∈ completeIdentityTopChartNodeKernel K n h m) : ∃ a : ℕ, (x) ^ a * z = 0 := by
  apply AffineOpenKernelPower.exists_pow_mul_eq_zero (l) (x) z
    (le_of_eq (completeIdentityTopChartSourceX_open K n h m))
  have hl := hz
  rw [completeIdentityTopChartNodeKernel, completeIdentityTopChartEvaluation_ker] at hl
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (S)[T;T⁻¹])).hom).injective
  change SpectrumGlobalRange.ringHom (l) z = (Scheme.ΓSpecIso _).hom 0
  rw [map_zero]
  exact hl.1

/-- Every kernel function is also killed by a power of the original incoming source coordinate. -/
theorem completeIdentityTopChartNodeKernel_y (z : Γ((H), ⊤))
    (hz : z ∈ completeIdentityTopChartNodeKernel K n h m) : ∃ b : ℕ, (y) ^ b * z = 0 := by
  apply AffineOpenKernelPower.exists_pow_mul_eq_zero (r) (y) z
    (le_of_eq (completeIdentityTopChartSourceY_open K n h m))
  have hr := hz
  rw [completeIdentityTopChartNodeKernel, completeIdentityTopChartEvaluation_ker] at hr
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (S)[T;T⁻¹])).hom).injective
  change SpectrumGlobalRange.ringHom (r) z = (Scheme.ΓSpecIso _).hom 0
  rw [map_zero]
  exact hr.2

/-- Both original coordinate powers annihilate each element of the actual remaining ideal. -/
theorem completeIdentityTopChartNodeKernel_powers (z : Γ((H), ⊤))
    (hz : z ∈ completeIdentityTopChartNodeKernel K n h m) :
    ∃ a b : ℕ, (x) ^ a * z = 0 ∧ (y) ^ b * z = 0 := by
  obtain ⟨a, ha⟩ := completeIdentityTopChartNodeKernel_x K n h m z hz
  obtain ⟨b, hb⟩ := completeIdentityTopChartNodeKernel_y K n h m z hz
  exact ⟨a, b, ha, hb⟩

end FLT.Mazur.PolygonInfinitesimalStages
