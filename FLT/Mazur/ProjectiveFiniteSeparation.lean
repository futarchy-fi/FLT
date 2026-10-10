/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceCharts
public import Mathlib.Order.Preorder.Finite

/-!
# Homogeneous separation of finitely many projective points

A homogeneous prime not containing any of the other prescribed primes can
be separated from all of them by a positive-degree homogeneous polynomial.
No infinitude assumption on the coefficient ring or residue fields is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry MvPolynomial

universe u v

namespace FLT.Mazur.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {ι : Type v}

/-- Failure of inclusion of homogeneous primes is witnessed by a homogeneous polynomial. -/
theorem exists_homogeneous_separator (p q : space R ι)
    (h : ¬ q.asHomogeneousIdeal.toIdeal ≤ p.asHomogeneousIdeal.toIdeal) :
    ∃ (n : ℕ) (f : MvPolynomial ι R), f.IsHomogeneous n ∧
      f ∈ q.asHomogeneousIdeal ∧ f ∉ p.asHomogeneousIdeal := by
  obtain ⟨f, hfq, hfp⟩ := IsConcreteLE.not_le_iff_exists.mp h
  have hp := p.asHomogeneousIdeal.isHomogeneous
  rw [mem_iff_homogeneousComponent_mem hp f] at hfp
  push Not at hfp
  obtain ⟨n, hn⟩ := hfp
  exact ⟨n, homogeneousComponent n f, homogeneousComponent_mem n f,
    homogeneousComponent_mem_of_mem q.asHomogeneousIdeal.isHomogeneous hfq n, hn⟩

/-- Simultaneously vanish on a finite set while avoiding a prime containing none of it. -/
theorem exists_homogeneous_finite_separator (p : space R ι) (T : Finset (space R ι))
    (hT : ∀ q ∈ T, ¬ q.asHomogeneousIdeal.toIdeal ≤ p.asHomogeneousIdeal.toIdeal) :
    ∃ (n : ℕ) (f : MvPolynomial ι R), 0 < n ∧ f.IsHomogeneous n ∧
      f ∉ p.asHomogeneousIdeal ∧ ∀ q ∈ T, f ∈ q.asHomogeneousIdeal := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    obtain ⟨i, hi⟩ := exists_mem_chart R ι p
    exact ⟨1, X i, by decide, isHomogeneous_X R i, hi, by simp⟩
  | @insert q T hq ih =>
    obtain ⟨n, f, hn, hf, hfp, hfT⟩ := ih (fun r hr ↦ hT r (Finset.mem_insert_of_mem hr))
    obtain ⟨m, g, hg, hgq, hgp⟩ :=
      exists_homogeneous_separator p q (hT q (Finset.mem_insert_self _ _))
    refine ⟨n + m, f * g, by omega, hf.mul hg, ?_, ?_⟩
    · exact fun h ↦ (p.isPrime.mem_or_mem h).elim hfp hgp
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact r.asHomogeneousIdeal.toIdeal.mul_mem_left f hgq
      · exact r.asHomogeneousIdeal.toIdeal.mul_mem_right g (hfT r hr)

end FLT.Mazur.ProjectiveSpace
