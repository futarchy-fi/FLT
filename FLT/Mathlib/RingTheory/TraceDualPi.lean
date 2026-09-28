/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Trace-dual lattices in products

The trace of a finite product is the sum of its component traces. Consequently,
the trace dual of a product lattice is the product of its trace duals.
-/

@[expose] public noncomputable section

open Module Algebra

/-- The trace of a finite product algebra is the sum of its component traces. -/
theorem Algebra.trace_pi_of_basis {R κ : Type*} [CommRing R] [Fintype κ]
    {C : κ → Type*} [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]
    {ι : κ → Type*} [∀ i, Finite (ι i)] (b : ∀ i, Basis (ι i) R (C i))
    (x : ∀ i, C i) : trace R (∀ i, C i) x = ∑ i, trace R (C i) (x i) := by
  classical
  let _ (i : κ) := Fintype.ofFinite (ι i)
  rw [trace_eq_matrix_trace (Pi.basis b)]
  simp only [Matrix.trace]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_eq_matrix_trace (b i)]
  simp only [Matrix.trace, Matrix.diag_apply, leftMulMatrix_eq_repr_mul, Pi.basis_repr,
    Pi.mul_apply, Pi.basis_apply, Pi.single_eq_same]

/-- The trace-dual construction acts componentwise on a product of lattices. -/
theorem Algebra.dualSubmodule_pi {A K κ : Type*} [CommRing A] [Field K]
    [Algebra A K] [Finite κ]
    {L : κ → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, Algebra A (L i)] [∀ i, IsScalarTower A K (L i)]
    [∀ i, FiniteDimensional K (L i)] (N : ∀ i, Submodule A (L i)) :
    (traceForm K (∀ i, L i)).dualSubmodule (Submodule.pi Set.univ N) =
      Submodule.pi Set.univ (fun i ↦ (traceForm K (L i)).dualSubmodule (N i)) := by
  classical
  let := Fintype.ofFinite κ
  have ht (x : ∀ i, L i) : trace K (∀ i, L i) x = ∑ i, trace K (L i) (x i) :=
    trace_pi_of_basis (fun i ↦ Module.finBasis K (L i)) x
  ext x
  constructor
  · intro hx
    change ∀ i ∈ Set.univ, ∀ y ∈ N i, traceForm K (L i) (x i) y ∈ (1 : Submodule A K)
    intro i _ y hy
    have hs : Pi.single i y ∈ Submodule.pi Set.univ N := by
      intro j _
      by_cases h : j = i
      · subst j
        simpa using hy
      · simp [Pi.single_eq_of_ne h]
    have h := hx (Pi.single i y) hs
    have he : traceForm K (∀ i, L i) x (Pi.single i y) =
        traceForm K (L i) (x i) y := by
      rw [traceForm_apply, ht, Fintype.sum_eq_single i]
      · simp only [Pi.mul_apply, Pi.single_eq_same, traceForm_apply]
      · intro j hji
        simp [Pi.single_eq_of_ne hji]
    rwa [he] at h
  · intro hx y hy
    rw [traceForm_apply, ht]
    apply Submodule.sum_mem
    intro i _
    exact hx i (Set.mem_univ i) (y i) (hy i (Set.mem_univ i))

/-- An algebra isomorphism transports trace-dual lattices along with the lattices. -/
theorem AlgEquiv.mem_dualSubmodule_map_iff
    {A K C D : Type*} [CommRing A] [Field K] [CommRing C] [CommRing D]
    [Algebra A K] [Algebra K C] [Algebra K D]
    [Algebra A C] [Algebra A D] [IsScalarTower A K C] [IsScalarTower A K D]
    (e : C ≃ₐ[K] D) (N : Submodule A C) (x : C) :
    e x ∈ (traceForm K D).dualSubmodule
      (N.map (e.toLinearEquiv.restrictScalars A).toLinearMap) ↔
      x ∈ (traceForm K C).dualSubmodule N := by
  constructor
  · intro hx y hy
    have h := hx (e y) (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
    simpa only [traceForm_apply, ← map_mul, trace_eq_of_algEquiv] using h
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    simpa only [traceForm_apply, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
      AlgEquiv.toLinearEquiv_apply, ← map_mul, trace_eq_of_algEquiv] using hx z hz
