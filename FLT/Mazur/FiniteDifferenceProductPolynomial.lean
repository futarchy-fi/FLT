/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoprimePolynomialContent
public import FLT.Mazur.FiniteDifferencePolynomial
public import FLT.Mazur.FiniteDifferenceProducts

/-!
# A single polynomial for a disjoint family of full endpoint equations

The coefficients of one product polynomial generate the exact product of
coordinate difference ideals. This replaces infinitely many mixed equations
by one finite polynomial equation, including over nonreduced correction rings.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.FiniteCoefficientDifference
variable {I B T : Type*} [Fintype I] [CommRing B] [CommRing T]
  (l r : I → B →+* T)

/-- A single polynomial over the unchanged source encoding all coordinate ideals. -/
def commonDifferencePolynomial [IsNoetherianRing T] : B[X] :=
  (exists_common_difference_polynomial l r).choose

/-- The common polynomial retains each exact endpoint difference ideal. -/
theorem commonDifferencePolynomial_content [IsNoetherianRing T] (i : I) :
    ((commonDifferencePolynomial l r).map (l i) -
      (commonDifferencePolynomial l r).map (r i)).contentIdeal =
        differenceIdeal (l i) (r i) :=
  (exists_common_difference_polynomial l r).choose_spec i

/-- Evaluate one original polynomial along every coordinate and multiply the differences. -/
def differenceProductPolynomial (P : B[X]) : T[X] :=
  ∏ i, (P.map (l i) - P.map (r i))

/-- Pairwise comaximality computes the full polynomial content without radicals. -/
theorem differenceProductPolynomial_content (P : B[X])
    (hP : ∀ i, (P.map (l i) - P.map (r i)).contentIdeal = differenceIdeal (l i) (r i))
    (hc : Pairwise fun i j ↦ IsCoprime (differenceIdeal (l i) (r i))
      (differenceIdeal (l j) (r j))) :
    (differenceProductPolynomial l r P).contentIdeal = ∏ i, differenceIdeal (l i) (r i) := by
  unfold differenceProductPolynomial
  rw [CoprimePolynomialContent.content_prod _ _ (fun i _ j _ hij ↦ by
    simpa only [hP] using hc hij)]
  simp_rw [hP]

/-- The constructed product polynomial has precisely the mixed-product ideal as its content. -/
theorem common_differenceProduct_content [IsNoetherianRing T]
    (hc : Pairwise fun i j ↦ IsCoprime (differenceIdeal (l i) (r i))
      (differenceIdeal (l j) (r j))) :
    (differenceProductPolynomial l r (commonDifferencePolynomial l r)).contentIdeal =
      ∏ i, differenceIdeal (l i) (r i) :=
  differenceProductPolynomial_content l r _ (commonDifferencePolynomial_content l r) hc

/-- Every correction ideal is tested by the same one finite polynomial. -/
theorem product_le_iff_common_polynomial [IsNoetherianRing T]
    (hc : Pairwise fun i j ↦ IsCoprime (differenceIdeal (l i) (r i))
      (differenceIdeal (l j) (r j))) (K : Ideal T) :
    (∏ i, differenceIdeal (l i) (r i)) ≤ K ↔
      (differenceProductPolynomial l r (commonDifferencePolynomial l r)).map
        (Ideal.Quotient.mk K) = 0 := by
  rw [← common_differenceProduct_content l r hc, ← contentIdeal_eq_bot_iff,
    contentIdeal_map_eq_map_contentIdeal, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

/-- The single polynomial detects all mixed equations after arbitrary coefficient base change. -/
theorem mixed_products_vanish_iff_polynomial [IsNoetherianRing T]
    (hc : Pairwise fun i j ↦ IsCoprime (differenceIdeal (l i) (r i))
      (differenceIdeal (l j) (r j))) {C : Type*} [CommRing C] (g : T →+* C) :
    (∀ a : I → B, g (∏ i, (l i (a i) - r i (a i))) = 0) ↔
      (differenceProductPolynomial l r (commonDifferencePolynomial l r)).map g = 0 := by
  change (∀ a : I → B, (∏ i, (l i (a i) - r i (a i))) ∈ RingHom.ker g) ↔ _
  rw [← product_differenceIdeal_le_iff, ← common_differenceProduct_content l r hc,
    ← contentIdeal_eq_bot_iff, contentIdeal_map_eq_map_contentIdeal,
    Ideal.map_eq_bot_iff_le_ker]

end FLT.Mazur.FiniteCoefficientDifference
