/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants from alternating pairings

A nonzero top-degree alternating map detects the determinant of an endomorphism,
even when its values lie in a module rather than the scalar field.
-/

@[expose] public section

namespace AlternatingMap

variable {R V W ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]

/-- A top-degree alternating map is determined by its value on a basis. -/
theorem apply_eq_det_smul (B : V [⋀^ι]→ₗ[R] W) (b : Module.Basis ι R V)
    (v : ι → V) : B v = b.det v • B b := by
  have h : B = (LinearMap.toSpanSingleton R W (B b)).compAlternatingMap b.det := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change B (b ∘ σ) = b.det (b ∘ σ) • B b
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  exact congrArg (fun f : V [⋀^ι]→ₗ[R] W => f v) h

omit [Fintype ι] [DecidableEq ι] in
/-- Applying an endomorphism in every input scales a top-degree pairing by its determinant. -/
theorem map_eq_det_smul [Finite ι] (B : V [⋀^ι]→ₗ[R] W) (b : Module.Basis ι R V)
    (f : V →ₗ[R] V) (v : ι → V) : B (f ∘ v) = f.det • B v := by
  classical
  let := Fintype.ofFinite ι
  rw [B.apply_eq_det_smul b (f ∘ v), B.apply_eq_det_smul b v,
    Module.Basis.det_comp, mul_smul]

variable {K : Type*} [Field K] [Module K V] [Module K W]

omit [Fintype ι] [DecidableEq ι] in
/-- The multiplier of a nonzero top-degree alternating pairing is the determinant. -/
theorem det_eq_of_similitude [Finite ι] (B : V [⋀^ι]→ₗ[K] W) (b : Module.Basis ι K V)
    (hB : B ≠ 0) (f : V →ₗ[K] V) (c : K)
    (h : ∀ v, B (f ∘ v) = c • B v) : f.det = c := by
  obtain ⟨v, hv⟩ : ∃ v, B v ≠ 0 := by
    by_contra! h
    exact hB (AlternatingMap.ext h)
  exact (smul_left_injective K hv) ((B.map_eq_det_smul b f v).symm.trans (h v))

end AlternatingMap
