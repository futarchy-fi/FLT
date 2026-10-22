/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreePolynomialNormSplitting
public import FLT.Mazur.FiniteBasisDifferencePolynomial
public import FLT.Mazur.SplitFrameDifferenceCoprime
public import FLT.Mazur.ScalarPolynomialNormEquation

/-!
# Full comparison equations from a complete finite free scalar source

The norm, its root equation, its splitting, and comaximality are all
constructed from a basis and a whole-source algebra decomposition.
The resulting mixed equations hold on arbitrary nonreduced test rings.
-/

@[expose] public noncomputable section
open Polynomial Module TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteFreeSplitComparisonEquation
open FiniteFreePolynomialNorm PolynomialTensorSplitFrame FiniteCoefficientDifference
set_option backward.isDefEq.respectTransparency false
variable {R B T I : Type*} [CommRing R] [CommRing B] [CommRing T]
  [Algebra R B] [Algebra R T] [Fintype I] {d : ℕ}
  (b : Basis (Fin d) R B) (e : (T ⊗[R] B) ≃ₐ[T] (I → T)) (y : B →ₐ[R] T)
include b

/-- The constructed scalar norm kills the comparison polynomial for every source polynomial. -/
theorem differenceProduct_eq_zero (P : B[X]) :
    differenceProductPolynomial (coordinate e) (fun _ ↦ y.toRingHom) P = 0 := by
  apply ScalarPolynomialNormEquation.differenceProduct_eq_zero
    (algebraMap R B) y.toRingHom y.toRingHom (coordinate e) rfl P
    (signedEquation (I := I) b P) (signedEquation_root b P)
  have hy : y.toRingHom.comp (algebraMap R B) = algebraMap R T := y.comp_algebraMap
  rw [hy]
  exact signedEquation_split b e P

/-- All mixed original coefficient equations vanish without Noetherianity or reducedness. -/
theorem mixed_products_eq_zero (a : I → B) :
    (∏ i, (coordinate e i (a i) - y (a i))) = 0 := by
  apply (product_differenceIdeal_eq_bot_iff (coordinate e) (fun _ ↦ y.toRingHom)).mp
    ?_ a
  rw [← differenceProductPolynomial_content (coordinate e) (fun _ ↦ y.toRingHom)
    (coefficientPolynomial b)
    (fun i ↦ basisPolynomial_content b (coordinateAlgHom e i) y)
    (differenceIdeal_pairwise_coprime e y.toRingHom),
    differenceProduct_eq_zero b e y, contentIdeal_zero]

/-- The whole product of original equality ideals vanishes, preserving nilpotents exactly. -/
theorem product_differenceIdeal_eq_bot :
    (∏ i, differenceIdeal (coordinate e i) y.toRingHom) = ⊥ := by
  rw [product_differenceIdeal_eq_bot_iff]
  exact mixed_products_eq_zero b e y

end FLT.Mazur.FiniteFreeSplitComparisonEquation
