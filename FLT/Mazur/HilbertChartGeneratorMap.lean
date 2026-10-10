/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartAlgebra
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Evaluation into the universal Hilbert chart algebra

The ambient generators define an actual polynomial evaluation homomorphism.
It is not yet surjective: the prescribed basis relations are imposed next.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)

instance : Algebra R (UniversalAlgebra R I d) :=
  Algebra.compHom _ (algebraMap R (Coefficients R I d))

instance : IsScalarTower R (Coefficients R I d) (UniversalAlgebra R I d) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := Coefficients R I d)
    (A := UniversalAlgebra R I d) fun _ ↦ rfl

/-- The actual universal vector assigned to an ambient generator. -/
def generator (i : I) : UniversalAlgebra R I d := generatorCoeff R I d i

/-- Evaluate ambient polynomials in the universal algebra. -/
def evaluation : MvPolynomial I R →ₐ[R] UniversalAlgebra R I d :=
  MvPolynomial.aeval (generator R I d)

/-- Evaluation on each ambient variable is its universal generator vector. -/
theorem evaluation_X (i : I) : evaluation R I d (MvPolynomial.X i) = generator R I d i :=
  MvPolynomial.aeval_X _ _

/-- The coordinates of an evaluated ambient variable are the parameter coordinates. -/
theorem coordinates_evaluation_X (i : I) (k : Fin d) :
    coordinates R I d (evaluation R I d (MvPolynomial.X i)) k =
      generatorCoeff R I d i k := by
  rw [evaluation_X]
  rfl

/-- Constants evaluate to their scalar multiple of the actual unit vector. -/
theorem coordinates_evaluation_C (r : R) (k : Fin d) :
    coordinates R I d (evaluation R I d (MvPolynomial.C r)) k =
      algebraMap R (Coefficients R I d) r * unitCoeff R I d k := by
  rw [evaluation, MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply R
    (Coefficients R I d) (UniversalAlgebra R I d), Algebra.algebraMap_eq_smul_one]
  rfl

/-- Evaluation of products follows the actual universal multiplication table. -/
theorem coordinates_evaluation_mul (p q : MvPolynomial I R) (k : Fin d) :
    coordinates R I d (evaluation R I d (p * q)) k =
      ∑ i, ∑ j, coordinates R I d (evaluation R I d p) i *
        coordinates R I d (evaluation R I d q) j * mulCoeff R I d i j k := by
  rw [map_mul, coordinates_mul]

/-- The polynomial map is uniquely specified by these generator vectors. -/
theorem evaluation_unique (f : MvPolynomial I R →ₐ[R] UniversalAlgebra R I d)
    (hf : ∀ i, f (MvPolynomial.X i) = generator R I d i) : f = evaluation R I d := by
  apply MvPolynomial.algHom_ext
  intro i
  exact (hf i).trans (evaluation_X R I d i).symm

end FLT.Mazur.HilbertChart
