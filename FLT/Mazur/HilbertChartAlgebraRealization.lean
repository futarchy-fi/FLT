/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartCoefficientMap
public import FLT.Mazur.HilbertChartGeneratorMap

/-!
# Realizing the universal algebra in an arbitrary based algebra

The coefficient map extends to an actual algebra homomorphism by sending the
universal coordinate basis to the given basis. Multiplicativity follows from
the extracted structure constants, and the universal generators are recovered.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable {S A : Type*} [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
variable [Algebra R A] [IsScalarTower R S A]
variable (v : Module.Basis (Fin d) S A) (x : I → A)

omit [Algebra R S] [Algebra R A] [IsScalarTower R S A] in
/-- The complete multiplication formula in an arbitrary actual basis. -/
theorem repr_mul_table (a b : A) (k : Fin d) :
    v.repr (a * b) k = ∑ i, ∑ j, v.repr a i * v.repr b j * structureCoeff v i j k := by
  conv_lhs => rw [← v.sum_repr a]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp_rw [repr_mul_basis_right, Finset.mul_sum, mul_assoc]

/-- Realize a universal vector using the coefficient map and the given actual basis. -/
def realizeVector (a : UniversalAlgebra R I d) : A :=
  v.equivFun.symm fun k ↦ readCoefficients R I d v x (coordinates R I d a k)

omit [Algebra R A] [IsScalarTower R S A] in
/-- Coordinates of a realized vector are obtained by the actual coefficient map. -/
theorem realizeVector_repr (a : UniversalAlgebra R I d) (k : Fin d) :
    v.repr (realizeVector R I d v x a) k =
      readCoefficients R I d v x (coordinates R I d a k) := by
  exact congrFun (v.equivFun.apply_symm_apply _) k

/-- The actual realization homomorphism from the universal based algebra. -/
def realization : UniversalAlgebra R I d →ₐ[R] A where
  toFun := realizeVector R I d v x
  map_one' := by
    apply v.ext_elem
    intro k
    rw [realizeVector_repr, coordinates_one, readCoefficients_unit]
    rfl
  map_mul' a b := by
    apply v.ext_elem
    intro k
    simp only [realizeVector_repr, coordinates_mul, map_sum, map_mul,
      readCoefficients_mul, repr_mul_table]
  map_zero' := by
    apply v.ext_elem
    intro k
    rw [realizeVector_repr]
    simp only [map_zero, Pi.zero_apply, Finsupp.zero_apply]
  map_add' a b := by
    apply v.ext_elem
    intro k
    simp only [realizeVector_repr, map_add, Pi.add_apply, Finsupp.add_apply]
  commutes' r := by
    apply v.ext_elem
    intro k
    rw [realizeVector_repr, IsScalarTower.algebraMap_apply R (Coefficients R I d)
      (UniversalAlgebra R I d), Algebra.algebraMap_eq_smul_one]
    change readCoefficients R I d v x
      (algebraMap R (Coefficients R I d) r * unitCoeff R I d k) = _
    rw [map_mul, AlgHom.commutes, readCoefficients_unit,
      IsScalarTower.algebraMap_apply R S A,
      Algebra.algebraMap_eq_smul_one (algebraMap R S r)]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, structureUnit]

/-- The universal generator vectors specialize to the original given vectors. -/
theorem realization_generator (i : I) :
    realization R I d v x (generator R I d i) = x i := by
  apply v.ext_elem
  intro k
  change v.repr (realizeVector R I d v x _) k = _
  rw [realizeVector_repr]
  exact readCoefficients_generator R I d v x i k

/-- The realization sends each distinguished universal basis vector to the given basis. -/
theorem realization_basis (i : Fin d) :
    realization R I d v x (basis R I d i) = v i := by
  apply v.ext_elem
  intro k
  change v.repr (realizeVector R I d v x _) k = _
  rw [realizeVector_repr, coordinates_basis, Module.Basis.repr_self_apply]
  split_ifs <;> simp only [map_one, map_zero]

/-- Evaluation of every original polynomial is recovered by the realization map. -/
theorem realization_evaluation (p : MvPolynomial I R) :
    realization R I d v x (evaluation R I d p) = MvPolynomial.aeval x p := by
  have h : (realization R I d v x).comp (evaluation R I d) = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, evaluation_X, realization_generator, MvPolynomial.aeval_X]
  exact AlgHom.congr_fun h p

end FLT.Mazur.HilbertChart
