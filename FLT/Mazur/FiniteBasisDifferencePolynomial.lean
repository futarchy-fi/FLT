/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteDifferencePolynomial
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# A fixed basis polynomial computes every scalar-compatible difference ideal

A finite basis of the original source gives one explicit polynomial for all
pairs of scalar-compatible endpoints. No Noetherian assumption on the test
ring is needed, and the polynomial is independent of the chosen endpoints.
-/

@[expose] public noncomputable section
open Polynomial Module
namespace FLT.Mazur.FiniteCoefficientDifference
set_option backward.isDefEq.respectTransparency false
variable {R B T : Type*} [CommRing R] [CommRing B] [CommRing T]
  [Algebra R B] [Algebra R T] {d : ℕ} (b : Basis (Fin d) R B)
  (l r : B →ₐ[R] T)

/-- Differences of the basis vectors generate the entire original difference ideal. -/
theorem differenceIdeal_eq_span_basis :
    differenceIdeal l.toRingHom r.toRingHom =
      Ideal.span (Set.range fun i ↦ l (b i) - r (b i)) := by
  apply le_antisymm
  · rw [differenceIdeal, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : l x - r x = ∑ i, b.repr x i • (l (b i) - r (b i)) := by
      conv_lhs => rw [← b.sum_repr x]
      simp only [map_sum, map_smul, Finset.sum_sub_distrib, smul_sub]
    change l x - r x ∈ Ideal.span _
    rw [hx]
    apply Submodule.sum_mem
    intro i _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span (Set.mem_range_self (b i))

/-- One fixed polynomial of original basis coefficients represents all full endpoint equations. -/
theorem basisPolynomial_content :
    ((coefficientPolynomial b).map l.toRingHom -
      (coefficientPolynomial b).map r.toRingHom).contentIdeal =
        differenceIdeal l.toRingHom r.toRingHom := by
  apply le_antisymm (polynomial_difference_content_le _ _ _)
  rw [differenceIdeal_eq_span_basis b l r, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have h := ((coefficientPolynomial b).map l.toRingHom -
    (coefficientPolynomial b).map r.toRingHom).coeff_mem_contentIdeal i.val
  simpa only [coeff_sub, coeff_map, coefficientPolynomial_coeff, SetLike.mem_coe] using! h

end FLT.Mazur.FiniteCoefficientDifference
