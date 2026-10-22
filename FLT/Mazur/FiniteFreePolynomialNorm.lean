/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeAlgebraCharpoly

/-!
# A bivariate characteristic equation from the whole finite free source

A polynomial of source coefficients defines an element of the polynomial
scalar extension of the entire algebra. Cayley-Hamilton constructs its
bivariate equation over the original scalars, without a reducedness assumption.
-/

@[expose] public noncomputable section
open Polynomial Module TensorProduct
namespace FLT.Mazur.FiniteFreePolynomialNorm
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
attribute [local instance] Polynomial.algebra

/-- The original polynomial as an element of the entire scalar-extended algebra. -/
def element (P : B[X]) : R[X] ⊗[R] B :=
  P.eval₂ Algebra.TensorProduct.includeRight.toRingHom
    (algebraMap R[X] (R[X] ⊗[R] B) X)

/-- Evaluation of tensor coefficients into the actual source polynomial ring. -/
def realization : (R[X] ⊗[R] B) →ₐ[R[X]] B[X] :=
  Algebra.TensorProduct.lift (Algebra.ofId R[X] B[X]) Polynomial.CAlgHom
    (fun _ _ ↦ Commute.all _ _)

/-- The tensor element retains every original polynomial coefficient. -/
theorem realization_element (P : B[X]) : realization (element (R := R) P) = P := by
  change (realization (R := R) (B := B)).toRingHom
    (P.eval₂ Algebra.TensorProduct.includeRight.toRingHom
    (algebraMap R[X] (R[X] ⊗[R] B) X)) = P
  rw [hom_eval₂]
  have hc : (realization (R := R) (B := B)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] R[X] ⊗[R] B).toRingHom = C := by
    ext b
    simp [realization]
  rw [hc]
  have hx : (realization (R := R) (B := B)).toRingHom (algebraMap R[X] (R[X] ⊗[R] B) X) =
      algebraMap R[X] B[X] X := (realization (R := R) (B := B)).commutes X
  rw [hx]
  change P.eval₂ C (X.map (algebraMap R B)) = P
  rw [map_X, eval₂_C_X]

variable {ι : Type*} [Finite ι] (b : Basis ι R B)

/-- A constructed bivariate polynomial over the prescribed scalar ring. -/
def equation (P : B[X]) : R[X][X] :=
  FiniteFreeAlgebraCharpoly.charpoly (b.baseChange R[X]) (element P)

/-- The equation has leading coefficient one, even on nonreduced sources. -/
theorem equation_monic (P : B[X]) : (equation b P).Monic :=
  FiniteFreeAlgebraCharpoly.monic _ _

/-- The constructed equation vanishes on the entire original polynomial. -/
theorem equation_root (P : B[X]) :
    ((equation b P).map (mapRingHom (algebraMap R B))).eval P = 0 := by
  have h := FiniteFreeAlgebraCharpoly.aeval_eq_zero (b.baseChange R[X]) (element P)
  have hz := congrArg realization h
  change (realization (R := R) (B := B)).toRingHom ((equation b P).eval₂
    (algebraMap R[X] (R[X] ⊗[R] B)) (element P)) = realization 0 at hz
  rw [hom_eval₂] at hz
  have hc : (realization (R := R) (B := B)).toRingHom.comp (algebraMap R[X] (R[X] ⊗[R] B)) =
      mapRingHom (algebraMap R B) := (realization (R := R) (B := B)).comp_algebraMap
  rw [hc] at hz
  change (equation b P).eval₂ (mapRingHom (algebraMap R B))
    (realization (element P)) = realization 0 at hz
  rw [realization_element, map_zero, eval₂_eq_eval_map] at hz
  exact hz

end FLT.Mazur.FiniteFreePolynomialNorm
