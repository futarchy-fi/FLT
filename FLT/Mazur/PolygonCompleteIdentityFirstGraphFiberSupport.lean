/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberSplit
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphSupport

/-!
# The residual special-fiber kernel is annihilated at the original node

Every element of the actual source conductor annihilates the remaining
square-zero fiber kernel. In particular uniform positive powers of both
original coordinates kill that kernel, without claiming it vanishes.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "r" => completeIdentityFirstGraphReduction K n h i
local notation "I" => completeIdentityFirstGraphParameterIdeal K n h i
local notation "Q" => completeIdentityFirstGraphSpecialFiber K n h i
local notation "q" => completeIdentityFirstGraphFiberQuotient K n h i
local notation "f" => completeIdentityFirstGraphFiberReduction K n h i
/-- The existing graph ring structure, cached for the conductor calculation. -/
local instance completeIdentityFirstGraphFiberSupportCommRing : CommRing (E) := inferInstance

/-- The exact source conductor kills the full residual square-zero special-fiber kernel. -/
theorem completeIdentityFirstGraphFiber_kernel_conductor (b : B)
    (hb : b ∈ completeIdentityFirstGraphConductorIdeal K n h i) (z : Q)
    (hz : (f) z = 0) : (q) ((s) b) * z = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have ha : a.val ∈ completeIdentityFirstGraphAlgebra K n h i := by
    rw [← completeIdentityFirstErrorAlgebra_eq_graph]
    exact a.property
  obtain ⟨w, hw⟩ := hb a.val ha
  have he : (s) w = (s) b * a := by
    apply Subtype.ext
    change firstNodeBranchPair (R) w = firstNodeBranchPair (R) b * a.val
    exact hw.trans (mul_comm _ _)
  have hw0 : firstNodeReduction (R) w = 0 := by
    rw [← completeIdentityFirstGraphReduction_source K n h i w, he, map_mul]
    change (r) ((s) b) * (r) a = 0
    change (r) a = 0 at hz
    rw [hz, mul_zero]
  change (q) ((s) b) * (q) a = (0 : Q)
  rw [← map_mul, ← he]
  exact completeIdentityFirstGraphFiberSource_kernel K n h i hw0

/-- One positive power of the original left coordinate annihilates the entire residual kernel. -/
theorem completeIdentityFirstGraphFiber_kernel_left :
    ∃ m : ℕ, 0 < m ∧ ∀ z : Q, (f) z = 0 →
      (q) ((s) (leftCoordinate (e))) ^ m * z = 0 := by
  obtain ⟨m, hm, hb⟩ := completeIdentityFirstGraphConductorIdeal_left K n h i
  refine ⟨m, hm, fun z hz ↦ ?_⟩
  simpa only [map_pow] using
    completeIdentityFirstGraphFiber_kernel_conductor K n h i _ hb z hz

/-- One positive power of the original right coordinate likewise kills the full kernel. -/
theorem completeIdentityFirstGraphFiber_kernel_right :
    ∃ m : ℕ, 0 < m ∧ ∀ z : Q, (f) z = 0 →
      (q) ((s) (rightCoordinate (e))) ^ m * z = 0 := by
  obtain ⟨m, hm, hb⟩ := completeIdentityFirstGraphConductorIdeal_right K n h i
  refine ⟨m, hm, fun z hz ↦ ?_⟩
  simpa only [map_pow] using
    completeIdentityFirstGraphFiber_kernel_conductor K n h i _ hb z hz

end FLT.Mazur.PolygonInfinitesimalStages
