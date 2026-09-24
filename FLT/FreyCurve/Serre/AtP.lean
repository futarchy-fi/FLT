/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep

/-!
# Comparing characters with an unramified local quotient

An inertia-invariant nonzero functional on a representation with two rank-one
constituents forces one of those same constituents to be inertia invariant.
This is the linear-algebra step in the at-p Serre argument. Constructing that
functional from semistable elliptic-curve reduction is a separate local input.
-/

@[expose] public section

namespace LinearMap

variable {k V G : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- If a representation filtered by two characters has a nonzero functional fixed
by a set of operators, one of its two characters is fixed by the entire set.
No splitting of the filtration is required. -/
theorem one_character_trivial_of_invariant_functional
    (ρ : G → Module.End k V) (χ₁ χ₂ : G → Module.End k k)
    (i : k →ₗ[k] V) (q : V →ₗ[k] k)
    (hexact : LinearMap.range i = LinearMap.ker q)
    (hi : ∀ g x, ρ g (i x) = i (χ₁ g x))
    (hq : ∀ g v, q (ρ g v) = χ₂ g (q v))
    (S : Set G) (r : V →ₗ[k] k) (hr : r ≠ 0)
    (hinv : ∀ g ∈ S, ∀ v, r (ρ g v) = r v) :
    (∀ g ∈ S, ∀ x, χ₁ g x = x) ∨ (∀ g ∈ S, ∀ x, χ₂ g x = x) := by
  classical
  have scalar (f : k →ₗ[k] k) (x : k) : f x = x * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul x 1
  by_cases hri : r (i 1) = 0
  · right
    have hker : ∀ v, q v = 0 → r v = 0 := by
      intro v hv
      obtain ⟨x, rfl⟩ := hexact.symm ▸ (show v ∈ LinearMap.ker q from hv)
      have hx : i x = x • i 1 := by
        simpa only [smul_eq_mul, mul_one] using i.map_smul x 1
      rw [hx, map_smul, hri, smul_zero]
    obtain ⟨v, hv⟩ : ∃ v, r v ≠ 0 := by
      by_contra! h
      exact hr (LinearMap.ext h)
    intro g hg x
    have hz : q (ρ g v - (χ₂ g 1) • v) = 0 := by
      rw [map_sub, hq, map_smul, scalar (χ₂ g), smul_eq_mul, mul_comm]
      exact sub_self _
    have heq := hker _ hz
    rw [map_sub, map_smul, hinv g hg, smul_eq_mul, sub_eq_zero] at heq
    have hone : χ₂ g 1 = 1 := (mul_right_cancel₀ hv (heq.symm.trans (one_mul _).symm))
    rw [scalar (χ₂ g), hone, mul_one]
  · left
    intro g hg x
    have heq : (χ₁ g x) * r (i 1) = x * r (i 1) := by
      calc
        _ = (r.comp i) (χ₁ g x) := (scalar (r.comp i) _).symm
        _ = (r.comp i) x :=
          (congrArg r (hi g x)).symm.trans (hinv g hg (i x))
        _ = _ := scalar (r.comp i) x
    exact mul_right_cancel₀ hri heq

end LinearMap
