/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeSplitCharpoly
public import FLT.Mazur.PolynomialTensorSplitFrame

/-!
# Constructed polynomial norms split on the whole frame

The bivariate norm comes from the unchanged finite free source algebra.
Its root identity and full-frame factorization are consequences of
Cayley-Hamilton and a complete scalar-extension decomposition.
-/

@[expose] public noncomputable section
open Polynomial Module TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteFreePolynomialNorm
open PolynomialTensorSplitFrame
variable {R B T I ι : Type*} [CommRing R] [CommRing B] [CommRing T]
  [Algebra R B] [Algebra R T] [Fintype I] [Finite ι]
  (b : Basis ι R B) (e : (T ⊗[R] B) ≃ₐ[T] (I → T))
attribute [local instance] Polynomial.algebra

/-- The actual full-frame algebra decomposition computes the constructed polynomial norm. -/
theorem equation_split (P : B[X]) :
    (equation b P).map (mapRingHom (algebraMap R T)) =
      ∏ i, (X - C (P.map (coordinate e i))) := by
  change (FiniteFreeAlgebraCharpoly.charpoly (b.baseChange R[X]) (element P)).map
    (algebraMap R[X] T[X]) = _
  rw [FiniteFreeAlgebraCharpoly.charpoly_split_baseChange _ _ (polynomialFrame e)]
  simp only [polynomialFrame_element]

/-- The signed convention used by the original comparison product. -/
def signedEquation (P : B[X]) : R[X][X] :=
  C ((-1 : R[X]) ^ Fintype.card I) * equation b P

/-- The signed norm retains its original source root identity. -/
theorem signedEquation_root (P : B[X]) :
    ((signedEquation (I := I) b P).map (mapRingHom (algebraMap R B))).eval P = 0 := by
  rw [signedEquation, Polynomial.map_mul, eval_mul, equation_root, mul_zero]

/-- Every frame coordinate occurs exactly once in the signed norm. -/
theorem signedEquation_split (P : B[X]) :
    (signedEquation (I := I) b P).map (mapRingHom (algebraMap R T)) =
      ∏ i, (C (P.map (coordinate e i)) - X) := by
  rw [signedEquation, Polynomial.map_mul, equation_split b e]
  simp only [map_pow, map_neg, map_one, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_one]
  have h : (∏ i, (C (P.map (coordinate e i)) - X)) =
      ∏ i, -(X - C (P.map (coordinate e i))) := by
    congr 1
    funext i
    exact (neg_sub _ _).symm
  rw [h]
  simpa only [Finset.card_univ] using
    (Finset.prod_neg (s := Finset.univ) (fun i ↦ X - C (P.map (coordinate e i)))).symm

end FLT.Mazur.FiniteFreePolynomialNorm
