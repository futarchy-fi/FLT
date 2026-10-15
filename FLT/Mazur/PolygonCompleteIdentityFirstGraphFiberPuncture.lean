/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberCoordinates
public import FLT.Mazur.SupportedReductionLocalization

/-!
# The actual graph special fiber away from its node

A power of the original coordinate sum annihilates the entire residual
kernel. Inverting this sum identifies the actual special fiber with the
unchanged punctured reduced node. The kernel of restriction is exactly
the residual kernel, so this construction does not silently discard it.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "Q" => completeIdentityFirstGraphSpecialFiber K n h i
local notation "f" => completeIdentityFirstGraphFiberReduction K n h i
local notation "x" => completeIdentityFirstGraphFiberLeft K n h i
local notation "y" => completeIdentityFirstGraphFiberRight K n h i

/-- A single power of the original coordinate sum kills the full residual fiber kernel. -/
theorem completeIdentityFirstGraphFiber_kernel_sum :
    ∃ k : ℕ, ∀ z : Q, (f) z = 0 → ((x) + (y)) ^ k * z = 0 := by
  obtain ⟨m, _, hm⟩ := completeIdentityFirstGraphFiber_kernel_left K n h i
  obtain ⟨j, _, hj⟩ := completeIdentityFirstGraphFiber_kernel_right K n h i
  exact SupportedReductionLocalization.sum_power (RingHom.ker (f)) (x) (y) m j hm hj

/-- The reduced original sum is regular on the entire unchanged reduced node. -/
theorem completeIdentityFirstGraphFiber_reduced_sum_regular :
    IsRegular ((f) ((x) + (y))) := by
  rw [map_add, completeIdentityFirstGraphFiberLeft_reduction,
    completeIdentityFirstGraphFiberRight_reduction]
  exact branchSum_regular (0 : R)

/-- The actual reduction gives an isomorphism on the original punctured special fiber. -/
def completeIdentityFirstGraphFiberPunctureEquiv :
    Localization.Away ((x) + (y)) ≃+* Localization.Away ((f) ((x) + (y))) :=
  SupportedReductionLocalization.awayEquiv (f)
    (completeIdentityFirstGraphFiberReduction_surjective K n h i) ((x) + (y))
    (completeIdentityFirstGraphFiber_kernel_sum K n h i)

/-- The puncture isomorphism is induced by the actual original reduction map. -/
theorem completeIdentityFirstGraphFiberPunctureEquiv_map :
    (completeIdentityFirstGraphFiberPunctureEquiv K n h i).toRingHom =
      Localization.awayMap (f) ((x) + (y)) := rfl

/-- Restriction to the actual puncture loses precisely the residual infinitesimal kernel. -/
theorem completeIdentityFirstGraphFiberPuncture_kernel :
    RingHom.ker (algebraMap (Q) (Localization.Away ((x) + (y)))) = RingHom.ker (f) :=
  SupportedReductionLocalization.localization_ker (f) ((x) + (y))
    (completeIdentityFirstGraphFiber_kernel_sum K n h i)
    (completeIdentityFirstGraphFiber_reduced_sum_regular K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
