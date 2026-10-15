/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberCoordinates
public import FLT.Mazur.SquareZeroReductionSocle

/-!
# The actual graph special fiber has a concrete node socle

The functions annihilated by both original coordinates form an actual
square-zero ideal of the literal special fiber. A nonreduced special
fiber necessarily contains a nonzero such function. This retains the
original graph and gives a node-supported witness to failure of descent.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing NilpotentIdealSocle
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

/-- The actual ideal of special-fiber functions killed by both original node coordinates. -/
def completeIdentityFirstGraphFiberSocle : Ideal (Q) := socle ⊤ (x) (y)

/-- Every original node socle function is in the residual square-zero kernel. -/
theorem completeIdentityFirstGraphFiberSocle_le :
    completeIdentityFirstGraphFiberSocle K n h i ≤ RingHom.ker (f) := by
  intro z hz
  apply completeIdentityFirstGraphFiber_sum_kernel K n h i
  rw [add_mul, hz.1.2, hz.2, add_zero]

/-- Multiplication of any two functions in the actual node socle is zero. -/
theorem completeIdentityFirstGraphFiberSocle_mul (z w : Q)
    (hz : z ∈ completeIdentityFirstGraphFiberSocle K n h i)
    (hw : w ∈ completeIdentityFirstGraphFiberSocle K n h i) : z * w = 0 :=
  completeIdentityFirstGraphFiberReduction_kernel_mul K n h i z w
    (completeIdentityFirstGraphFiberSocle_le K n h i hz)
    (completeIdentityFirstGraphFiberSocle_le K n h i hw)

/-- The full node socle is exactly the simultaneous annihilator inside the residual kernel. -/
theorem completeIdentityFirstGraphFiberSocle_eq :
    completeIdentityFirstGraphFiberSocle K n h i = socle (RingHom.ker (f)) (x) (y) := by
  apply le_antisymm
  · intro z hz
    exact ⟨⟨completeIdentityFirstGraphFiberSocle_le K n h i hz, hz.1.2⟩, hz.2⟩
  · intro z hz
    exact ⟨⟨Submodule.mem_top, hz.1.2⟩, hz.2⟩

/-- Killing just the node socle kills every residual infinitesimal function. -/
theorem completeIdentityFirstGraphFiber_reduced_iff_socle :
    IsReduced (Q) ↔ completeIdentityFirstGraphFiberSocle K n h i = ⊥ := by
  let _ := splitNodeBranchPair_isReduced (R)
  obtain ⟨m, _, hm⟩ := completeIdentityFirstGraphFiber_kernel_left K n h i
  obtain ⟨j, _, hj⟩ := completeIdentityFirstGraphFiber_kernel_right K n h i
  rw [completeIdentityFirstGraphFiberSocle_eq]
  exact SquareZeroReductionSocle.reduced_iff_socle_eq_bot (f)
    (fun z hz ↦ completeIdentityFirstGraphFiberReduction_kernel_mul K n h i z z hz hz)
    (x) (y) m j hm hj

/-- A nonreduced actual fiber supplies a nonzero square-zero function killed by x and y. -/
theorem completeIdentityFirstGraphFiber_nonreduced_witness (hn : ¬ IsReduced (Q)) :
    ∃ z : Q, z ≠ 0 ∧ (x) * z = 0 ∧ (y) * z = 0 ∧ z * z = 0 := by
  have hs : completeIdentityFirstGraphFiberSocle K n h i ≠ ⊥ :=
    fun he ↦ hn ((completeIdentityFirstGraphFiber_reduced_iff_socle K n h i).mpr he)
  obtain ⟨z, hz, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  exact ⟨z, hne, hz.1.2, hz.2, completeIdentityFirstGraphFiberSocle_mul K n h i z z hz hz⟩

end FLT.Mazur.PolygonInfinitesimalStages
