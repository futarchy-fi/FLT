/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RepresentationTheory.Basic

/-! # Algebra for the three-adic argument

A square-zero unipotent element has cube one in characteristic three. An invariant
surjective functional splits an extension with trivial subrepresentation and
nontrivial one-dimensional quotient, giving a stable complementary kernel.
-/

@[expose] public section

namespace GaloisRepresentation

/-- A square-zero unipotent element in characteristic three has cube one. -/
theorem cube_eq_one_of_sub_one_sq_eq_zero
    {A : Type*} [Ring A] [CharP A 3] (u : A)
    (hu : (u - 1) ^ 2 = 0) : u ^ 3 = 1 := by
  have hcube : (u - 1) ^ 3 = 0 := by rw [pow_succ, hu, zero_mul]
  calc
    u ^ 3 = (1 + (u - 1)) ^ 3 := by rw [add_comm 1, sub_add_cancel]
    _ = 1 ^ 3 + (u - 1) ^ 3 := add_pow_char_of_commute 3 (Commute.one_left _)
    _ = 1 := by rw [hcube, one_pow, add_zero]

-- Retain the full exact-sequence interface, including the redundant hypotheses.
set_option linter.unusedVariables false in
/-- An invariant surjective functional retracts the trivial subrepresentation
when the one-dimensional quotient character is nontrivial. -/
@[nolint unusedArguments]
theorem equivariant_retraction_of_trivial_quotient
    {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (i : k →ₗ[k] V) (q : V →ₗ[k] k)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : LinearMap.range i = LinearMap.ker q)
    (hiG : ∀ g x, ρ g (i x) = i x)
    (hqG : ∀ g v, q (ρ g v) = (χ g : k) * q v)
    (hne : ∃ g, χ g ≠ 1)
    (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hπG : ∀ g v, π (ρ g v) = π v) :
    ∃ r : V →ₗ[k] k, r.comp i = LinearMap.id ∧ ∀ g v, r (ρ g v) = r v := by
  have hnonzero : π (i 1) ≠ 0 := by
    intro hzero
    have hker : ∀ v ∈ LinearMap.ker q, π v = 0 := by
      intro v hv
      rw [← hex] at hv
      obtain ⟨x, rfl⟩ := hv
      have hx : i x = x • i 1 := by simpa using i.map_smul x (1 : k)
      rw [hx, map_smul, hzero, smul_zero]
    obtain ⟨g, hg⟩ := hne
    obtain ⟨v, hv⟩ := hπ 1
    have hdiff : ρ g v - (χ g : k) • v ∈ LinearMap.ker q := by
      simp [LinearMap.mem_ker, hqG, smul_eq_mul]
    have hchar := hker _ hdiff
    rw [map_sub, map_smul, hπG, hv, smul_eq_mul, mul_one] at hchar
    exact hg (Units.ext (sub_eq_zero.mp hchar).symm)
  refine ⟨(π (i 1))⁻¹ • π, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    have hx : i x = x • i 1 := by simpa using i.map_smul x (1 : k)
    simp [hx, smul_eq_mul, mul_left_comm, hnonzero]
  · intro g v
    simp only [LinearMap.smul_apply, hπG]

/-- The retraction's kernel is a stable complement of the trivial subrepresentation. -/
theorem stable_complement_of_trivial_quotient
    {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (i : k →ₗ[k] V) (q : V →ₗ[k] k)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : LinearMap.range i = LinearMap.ker q)
    (hiG : ∀ g x, ρ g (i x) = i x)
    (hqG : ∀ g v, q (ρ g v) = (χ g : k) * q v)
    (hne : ∃ g, χ g ≠ 1)
    (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hπG : ∀ g v, π (ρ g v) = π v) :
    ∃ r : V →ₗ[k] k, r.comp i = LinearMap.id ∧
      (∀ g v, r (ρ g v) = r v) ∧
      IsCompl (LinearMap.range i) (LinearMap.ker r) ∧
      ∀ g v, v ∈ LinearMap.ker r → ρ g v ∈ LinearMap.ker r := by
  obtain ⟨r, hr, hrG⟩ := equivariant_retraction_of_trivial_quotient
    ρ χ i q hi hq hex hiG hqG hne π hπ hπG
  have hri (x : k) : r (i x) = x := LinearMap.congr_fun hr x
  refine ⟨r, hr, hrG, ⟨?_, ?_⟩, ?_⟩
  · rw [disjoint_iff_inf_le]
    rintro v ⟨⟨x, rfl⟩, hx⟩
    change r (i x) = 0 at hx
    have hxzero : x = 0 := by simpa only [hri] using hx
    simp [hxzero]
  · rw [codisjoint_iff_le_sup]
    intro v _
    apply Submodule.mem_sup.mpr
    refine ⟨i (r v), ⟨r v, rfl⟩, v - i (r v), ?_, add_sub_cancel _ _⟩
    simp [LinearMap.mem_ker, hri]
  · intro g v hv
    simpa only [LinearMap.mem_ker, hrG] using hv

end GaloisRepresentation
