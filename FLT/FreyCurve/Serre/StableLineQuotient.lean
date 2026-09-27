/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.ReducibleFiltration

/-!
# Quotients by a specified stable line

A stable line in a two-dimensional representation gives a character quotient with
that line as its kernel. Inertia invariance of this quotient is equivalent to
inertia acting as the identity modulo the specified line.
-/

@[expose] public section

namespace GaloisRep

variable {K k V : Type*} [Field K] [Field k] [TopologicalSpace k]
  [DiscreteTopology k] [AddCommGroup V] [Module k V]

/-- Stability of the image of `1` suffices to make the image of a linear map
from the scalar field into a subrepresentation. -/
def stableLine (ρ : GaloisRep K k V) (i : k →ₗ[k] V)
    (hi : ∀ g, ∃ a, ρ g (i 1) = i a) : Subrepresentation ρ.toRepresentation where
  toSubmodule := LinearMap.range i
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, ha⟩ := hi g
    change ρ g (i x) ∈ LinearMap.range i
    have hx : i x = x • i 1 := by
      simpa only [smul_eq_mul, mul_one] using i.map_smul x 1
    rw [hx, map_smul, ha, ← map_smul]
    exact LinearMap.mem_range_self i _

/-- The quotient by a specified stable line in dimension two is a continuous
character. Its kernel is the given line, with no choice of a replacement line. -/
theorem exists_character_quotient_of_stableLine (ρ : GaloisRep K k V)
    (hdim : Module.finrank k V = 2) (i : k →ₗ[k] V)
    (hinj : Function.Injective i) (hi : ∀ g, ∃ a, ρ g (i 1) = i a) :
    ∃ (χ : GaloisRep K k k) (q : V →ₗ[k] k),
      Function.Surjective q ∧ LinearMap.ker q = LinearMap.range i ∧
      ∀ g x, q (ρ g x) = χ g (q x) := by
  classical
  have : FiniteDimensional k V := FiniteDimensional.of_finrank_eq_succ hdim
  let S := ρ.stableLine i hi
  have hS : Module.finrank k S.toSubmodule = 1 := by
    change Module.finrank k (LinearMap.range i) = 1
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_self]
  have hQ : Module.finrank k (V ⧸ S.toSubmodule) = 1 := by
    have := S.toSubmodule.finrank_quotient_add_finrank
    omega
  let e : (V ⧸ S.toSubmodule) ≃ₗ[k] k := LinearEquiv.ofFinrankEq _ _ (by simpa using hQ)
  refine ⟨(ρ.onQuotient S).conj e, e.toLinearMap.comp S.toSubmodule.mkQ,
    e.surjective.comp S.toSubmodule.mkQ_surjective, ?_, ?_⟩
  · ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, conj_apply_apply,
      LinearEquiv.symm_apply_apply]
    rfl

/-- If inertia acts trivially modulo a specified stable line, the character
quotient by that line is a nonzero inertia-invariant functional. -/
theorem exists_invariant_functional_of_stableLine (ρ : GaloisRep K k V)
    (hdim : Module.finrank k V = 2) (i : k →ₗ[k] V)
    (hinj : Function.Injective i) (hi : ∀ g, ∃ a, ρ g (i 1) = i a)
    (I : Set (Field.absoluteGaloisGroup K))
    (hI : ∀ g ∈ I, ∀ x, ρ g x - x ∈ LinearMap.range i) :
    ∃ q : V →ₗ[k] k, q ≠ 0 ∧ LinearMap.ker q = LinearMap.range i ∧
      ∀ g ∈ I, ∀ x, q (ρ g x) = q x := by
  obtain ⟨χ, q, hq, hker, _⟩ := ρ.exists_character_quotient_of_stableLine hdim i hinj hi
  refine ⟨q, ?_, hker, ?_⟩
  · obtain ⟨x, hx⟩ := hq 1
    intro h
    exact zero_ne_one ((LinearMap.congr_fun h x).symm.trans hx)
  · intro g hg x
    have h : ρ g x - x ∈ LinearMap.ker q := hker.symm ▸ hI g hg x
    simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using h

end GaloisRep
