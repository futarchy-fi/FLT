/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoefficientDifferenceIdeal
public import Mathlib.RingTheory.Polynomial.ContentIdeal

/-!
# One original polynomial encoding finitely many full endpoint equations

Noetherianity of the coefficient test supplies one polynomial in the original
source ring whose coefficients generate every full endpoint difference ideal.
The same polynomial works for all coordinates, without finite generation of
the source ring and without replacing the coefficient test by its reduction.
-/

@[expose] public noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FiniteCoefficientDifference
variable {B T : Type*} [CommRing B] [CommRing T]

/-- Pack a finite coefficient vector into a polynomial over the original ring. -/
def coefficientPolynomial {d : ℕ} (z : Fin d → B) : B[X] :=
  ∑ j : Fin d, Polynomial.monomial j.val (z j)

/-- Packing retains each prescribed coefficient exactly. -/
theorem coefficientPolynomial_coeff {d : ℕ} (z : Fin d → B) (j : Fin d) :
    (coefficientPolynomial z).coeff j.val = z j := by
  classical
  simp [coefficientPolynomial, finsetSum_coeff, coeff_monomial, Fin.val_inj]

/-- Every coefficient of a polynomial endpoint difference is an original difference. -/
theorem polynomial_difference_content_le (l r : B →+* T) (P : B[X]) :
    (P.map l - P.map r).contentIdeal ≤ differenceIdeal l r := by
  rw [contentIdeal_def, Ideal.span_le]
  intro x hx
  obtain ⟨j, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
  simp only [coeff_sub, coeff_map]
  exact Ideal.subset_span (Set.mem_range_self _)

/-- A polynomial containing a generating list computes the entire difference ideal. -/
theorem polynomial_difference_content_eq [IsNoetherianRing T]
    (l r : B →+* T) (P : B[X])
    (h : ∀ b ∈ coefficients l r, ∃ j : ℕ, P.coeff j = b) :
    (P.map l - P.map r).contentIdeal = differenceIdeal l r := by
  apply le_antisymm (polynomial_difference_content_le l r P)
  rw [differenceIdeal_eq, Ideal.span_le]
  rintro x ⟨b, hb, rfl⟩
  obtain ⟨j, hj⟩ := h b hb
  have hc := (P.map l - P.map r).coeff_mem_contentIdeal j
  simpa only [coeff_sub, coeff_map, hj, SetLike.mem_coe] using hc

/-- Construct one original polynomial encoding every full coordinate ideal at once. -/
theorem exists_common_difference_polynomial {I : Type*} [Finite I]
    [IsNoetherianRing T] (l r : I → B →+* T) :
    ∃ P : B[X], ∀ i, (P.map (l i) - P.map (r i)).contentIdeal =
      differenceIdeal (l i) (r i) := by
  classical
  let _ := Fintype.ofFinite I
  let s : Finset B := Finset.univ.biUnion fun i ↦ coefficients (l i) (r i)
  let z : Fin (Fintype.card s) → B := fun j ↦ ((Fintype.equivFin s).symm j).val
  refine ⟨coefficientPolynomial z, fun i ↦ polynomial_difference_content_eq _ _ _ ?_⟩
  intro b hb
  have hs : b ∈ s := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hb⟩
  let j := Fintype.equivFin s ⟨b, hs⟩
  refine ⟨j.val, (coefficientPolynomial_coeff z j).trans ?_⟩
  exact congrArg Subtype.val ((Fintype.equivFin s).symm_apply_apply ⟨b, hs⟩)

end FLT.Mazur.FiniteCoefficientDifference
