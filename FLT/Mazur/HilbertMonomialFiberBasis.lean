/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Monomial bases in finite-dimensional polynomial quotients

A spanning family contains a basis of the prescribed finite dimension. Applied
to monomial images, this produces ambient tuples without assuming a chosen basis.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

/-- Extract an ordered basis from any spanning family in a finite-dimensional vector space. -/
theorem exists_basis_from_spanning_family {K V A : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (x : A → V)
    (hx : Submodule.span K (Set.range x) = ⊤) (d : ℕ) (hd : Module.finrank K V = d) :
    ∃ a : Fin d → A, ∃ b : Module.Basis (Fin d) K V, ∀ i, b i = x (a i) := by
  classical
  let b := Module.Basis.ofSpan hx.ge
  let c := b.reindex (b.indexEquiv (Module.finBasisOfFinrankEq K V hd))
  have hc : ∀ i, c i ∈ Set.range x := by
    intro i
    dsimp only [c]
    rw [Module.Basis.reindex_apply]
    exact Module.Basis.ofSpan_subset hx.ge ⟨_, rfl⟩
  choose a ha using hc
  exact ⟨a, c, fun i ↦ (ha i).symm⟩

/-- The actual monomial images span every polynomial quotient. -/
theorem quotient_monomials_span (K I : Type*) [CommRing K]
    (J : Ideal (MvPolynomial I K)) :
    Submodule.span K (Set.range (fun m : I →₀ ℕ ↦
      Ideal.Quotient.mk J (MvPolynomial.monomial m (1 : K)))) = ⊤ := by
  let q := (Ideal.Quotient.mkₐ K J).toLinearMap
  have h := congrArg (Submodule.map q) (MvPolynomial.basisMonomials I K).span_eq
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr
    (Ideal.Quotient.mkₐ_surjective K J)] at h
  simpa only [MvPolynomial.coe_basisMonomials, ← Set.range_comp, Function.comp_def,
    q, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] using h

/-- A finite-dimensional quotient has a basis consisting of images of ambient monomials. -/
theorem exists_quotient_monomial_basis (K I : Type*) [Field K]
    (J : Ideal (MvPolynomial I K)) [Module.Finite K (MvPolynomial I K ⧸ J)]
    (d : ℕ) (hd : Module.finrank K (MvPolynomial I K ⧸ J) = d) :
    ∃ m : Fin d → (I →₀ ℕ), ∃ b : Module.Basis (Fin d) K (MvPolynomial I K ⧸ J),
      ∀ i, b i = Ideal.Quotient.mk J (MvPolynomial.monomial (m i) (1 : K)) :=
  exists_basis_from_spanning_family _ (quotient_monomials_span K I J) d hd

end FLT.Mazur.HilbertChart
