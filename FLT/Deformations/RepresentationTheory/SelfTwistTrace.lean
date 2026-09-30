/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic

/-!
# Trace support of a self-twist

If a representation is conjugate to its twist by a character, its trace
vanishes away from the kernel of that character. This is the elementary
trace calculation used after constructing a quadratic self-twist from a
reducible restriction. It does not construct the twist or prove that
restriction preserves irreducibility.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- The trace of a self-twist is supported on the kernel of its character. -/
theorem trace_eq_zero_of_selfTwist
    (χ : G →* kˣ) (e : V ≃ₗ[k] V)
    (he : ∀ g, e.conj (ρ g) = (χ g : k) • ρ g)
    (g : G) (hg : χ g ≠ 1) : LinearMap.trace k V (ρ g) = 0 := by
  have ht := LinearMap.trace_conj' (ρ g) e
  rw [he g, map_smul, smul_eq_mul] at ht
  have hz : ((χ g : k) - 1) * LinearMap.trace k V (ρ g) = 0 := by
    rw [sub_mul, one_mul, ht, sub_self]
  refine (mul_eq_zero.mp hz).resolve_left ?_
  intro h
  apply hg
  exact Units.ext (sub_eq_zero.mp h)

/-- A nonzero trace forces a self-twisting character to be trivial at that element. -/
theorem selfTwist_eq_one_of_trace_ne_zero
    (χ : G →* kˣ) (e : V ≃ₗ[k] V)
    (he : ∀ g, e.conj (ρ g) = (χ g : k) • ρ g)
    (g : G) (hg : LinearMap.trace k V (ρ g) ≠ 0) : χ g = 1 := by
  by_contra h
  exact hg (ρ.trace_eq_zero_of_selfTwist χ e he g h)

end Representation
