/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteDifferenceProductPolynomial

/-!
# Original scalar norm equations annihilate the full comparison polynomial

A polynomial with coefficients in the original scalar ring, split along the
whole first frame and vanishing at the original section, forces the exact
comparison polynomial to vanish. All coefficient rings may be nonreduced.
Constructing the scalar norm and its splitting remains a geometric obligation.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.ScalarPolynomialNormEquation
variable {I R B T : Type*} [Fintype I] [CommRing R] [CommRing B] [CommRing T]
  (σ : R →+* B) (x y : B →+* T) (l : I → B →+* T)
  (hxy : x.comp σ = y.comp σ) (P : B[X]) (N : R[X][X])
  (hroot : (N.map (Polynomial.mapRingHom σ)).eval P = 0)
  (hsplit : N.map (Polynomial.mapRingHom (x.comp σ)) =
    ∏ i, (Polynomial.C (P.map (l i)) - Polynomial.X))

include hxy hroot hsplit

/-- A split norm over original scalars kills the exact product polynomial on the whole test. -/
theorem differenceProduct_eq_zero :
    FiniteCoefficientDifference.differenceProductPolynomial l (fun _ ↦ y) P = 0 := by
  have hmap : N.map (Polynomial.mapRingHom (x.comp σ)) =
      (N.map (Polynomial.mapRingHom σ)).map (Polynomial.mapRingHom y) := by
    rw [hxy, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hz : (N.map (Polynomial.mapRingHom (x.comp σ))).eval (P.map y) = 0 := by
    rw [hmap]
    change ((N.map (Polynomial.mapRingHom σ)).map (Polynomial.mapRingHom y)).eval
      (Polynomial.mapRingHom y P) = 0
    rw [Polynomial.eval_map_apply, hroot, map_zero]
  rw [hsplit, Polynomial.eval_prod] at hz
  simpa only [FiniteCoefficientDifference.differenceProductPolynomial, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X] using hz

/-- With comaximal frame ideals, the scalar norm kills every original mixed coefficient product. -/
theorem mixed_products_eq_zero
    (hP : ∀ i, (P.map (l i) - P.map y).contentIdeal =
      FiniteCoefficientDifference.differenceIdeal (l i) y)
    (hc : Pairwise fun i j ↦ IsCoprime
      (FiniteCoefficientDifference.differenceIdeal (l i) y)
      (FiniteCoefficientDifference.differenceIdeal (l j) y)) :
    ∀ a : I → B, (∏ i, (l i (a i) - y (a i))) = 0 := by
  apply (FiniteCoefficientDifference.product_differenceIdeal_eq_bot_iff l (fun _ ↦ y)).mp
  rw [← FiniteCoefficientDifference.differenceProductPolynomial_content l (fun _ ↦ y)
    P hP hc, differenceProduct_eq_zero σ x y l hxy P N hroot hsplit,
    Polynomial.contentIdeal_zero]

end FLT.Mazur.ScalarPolynomialNormEquation
