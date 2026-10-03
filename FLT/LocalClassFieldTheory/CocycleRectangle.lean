/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.KernelCocycleNormalization

/-!
# Changing the vertices of a two-cocycle

Three applications of the cocycle equation compare a pair of edges before and
after changing its three vertices. This is the local formula for independence
of coset representatives in transfer.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- The explicit prism identity for a two-cocycle and three changes of vertices. -/
theorem twoCocycle_rectangle (c : G × G → M) (hc : IsCocycle₂ c) (a b r s t : G) :
    r • c (r⁻¹ * a * s, s⁻¹ * b * t) = c (a, b) +
      a • (c (s, s⁻¹ * b * t) - c (b, t)) -
      (c (r, r⁻¹ * (a * b) * t) - c (a * b, t)) +
      (c (r, r⁻¹ * a * s) - c (a, s)) := by
  have h₁ := hc r (r⁻¹ * a * s) (s⁻¹ * b * t)
  have h₂ := hc a s (s⁻¹ * b * t)
  have h₃ := hc a b t
  simp only [mul_assoc, mul_inv_cancel_left] at h₁ h₂ ⊢
  rw [eq_sub_of_add_eq h₁.symm, eq_sub_of_add_eq h₂, eq_sub_of_add_eq' h₃.symm,
    smul_sub]
  abel

end LocalClassFieldTheory
