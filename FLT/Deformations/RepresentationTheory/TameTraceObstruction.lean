/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.SelfTwistTrace
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Eigenvalue ratios obstruct nontrivial self-twists

Two nonzero eigenvalues with ratio of order greater than two have nonzero
sum. Consequently, a self-twisting character is trivial at an element
with this trace. The specializations to orders `p-1` and `p+1` provide the
last scalar calculation for the ordinary and niveau-two tame spectra.

The finite-flat inertia classification and the construction of an inertia
element with these eigenvalues remain separate arithmetic obligations.
-/

@[expose] public section

namespace Representation

variable {k : Type*} [Field k]

/-- Opposite eigenvalues have ratio of order at most two. -/
theorem add_ne_zero_of_orderOf_div_gt_two (a b : kˣ)
    (h : 2 < orderOf (a / b)) : (a : k) + (b : k) ≠ 0 := by
  intro hzero
  have hab : (a : k) = -(b : k) := eq_neg_of_add_eq_zero_left hzero
  have hpow : (a / b) ^ 2 = 1 := by
    apply Units.ext
    simp [hab]
  have hle := orderOf_le_of_pow_eq_one (by decide : 0 < 2) hpow
  omega

variable {G V : Type*} [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- A tame eigenvalue ratio of order greater than two detects triviality of a self-twist. -/
theorem selfTwist_eq_one_of_tame_eigenvalues
    (χ : G →* kˣ) (e : V ≃ₗ[k] V)
    (he : ∀ g, e.conj (ρ g) = (χ g : k) • ρ g)
    (g : G) (a b : kˣ)
    (htrace : LinearMap.trace k V (ρ g) = (a : k) + (b : k))
    (horder : 2 < orderOf (a / b)) : χ g = 1 := by
  apply ρ.selfTwist_eq_one_of_trace_ne_zero χ e he g
  rw [htrace]
  exact add_ne_zero_of_orderOf_div_gt_two a b horder

/-- The ordinary tame spectrum, once supplied, excludes a nontrivial twist at its generator. -/
theorem selfTwist_eq_one_of_order_eq_sub_one
    {p : ℕ} (hp : 17 ≤ p)
    (χ : G →* kˣ) (e : V ≃ₗ[k] V)
    (he : ∀ g, e.conj (ρ g) = (χ g : k) • ρ g)
    (g : G) (a b : kˣ)
    (htrace : LinearMap.trace k V (ρ g) = (a : k) + (b : k))
    (horder : orderOf (a / b) = p - 1) : χ g = 1 := by
  apply ρ.selfTwist_eq_one_of_tame_eigenvalues χ e he g a b htrace
  omega

/-- The niveau-two tame spectrum, once supplied, excludes a nontrivial twist at its generator. -/
theorem selfTwist_eq_one_of_order_eq_add_one
    {p : ℕ} (hp : 17 ≤ p)
    (χ : G →* kˣ) (e : V ≃ₗ[k] V)
    (he : ∀ g, e.conj (ρ g) = (χ g : k) • ρ g)
    (g : G) (a b : kˣ)
    (htrace : LinearMap.trace k V (ρ g) = (a : k) + (b : k))
    (horder : orderOf (a / b) = p + 1) : χ g = 1 := by
  apply ρ.selfTwist_eq_one_of_tame_eigenvalues χ e he g a b htrace
  omega

end Representation
