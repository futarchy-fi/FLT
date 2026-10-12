/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartStructureConstants
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Recovering multiplication coordinates from ambient generator actions

A subalgebra containing the matrices of multiplication by the ambient generators
contains the matrix of every original polynomial. When prescribed polynomials
are a basis, this recovers every multiplication coefficient without dividing or
changing the coefficient algebra.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.HilbertChart
variable {R S A I : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  {d : ℕ} (v : Module.Basis (Fin d) S A) (D : Subalgebra R S)

omit [Algebra R A] [IsScalarTower R S A] in
/-- A matrix with entries in a subalgebra preserves vectors with entries there. -/
theorem repr_mul_mem_of_matrix (b : A)
    (hb : ∀ j k, v.repr (v j * b) k ∈ D) (a : A)
    (ha : ∀ j, v.repr a j ∈ D) (k : Fin d) : v.repr (a * b) k ∈ D := by
  have h : v.repr (a * b) k = ∑ j, v.repr a j * v.repr (v j * b) k := by
    conv_lhs => rw [← v.sum_repr a]
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [h]
  exact D.sum_mem fun j _ ↦ D.mul_mem (ha j) (hb j k)

/-- Generator action matrices generate the entries of every polynomial action matrix. -/
theorem polynomial_action_coordinates_mem (x : I → A)
    (hx : ∀ i j k, v.repr (v j * x i) k ∈ D)
    (p : MvPolynomial I R) (j k : Fin d) :
    v.repr (v j * MvPolynomial.aeval x p) k ∈ D := by
  induction p using MvPolynomial.induction_on generalizing k with
  | C r =>
    rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply R S A,
      mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self_apply]
    split_ifs <;> simp only [mul_one, mul_zero]
    · exact D.algebraMap_mem r
    · exact D.zero_mem
  | add p q hp hq =>
    simpa only [map_add, mul_add, Finsupp.add_apply] using D.add_mem (hp k) (hq k)
  | mul_X p i hp =>
    rw [map_mul (MvPolynomial.aeval x), MvPolynomial.aeval_X, ← mul_assoc]
    exact repr_mul_mem_of_matrix v D (x i) (hx i) _ (fun l ↦ hp l) k

/-- A polynomial basis recovers the entire multiplication table from generator actions. -/
theorem structure_coordinates_mem_of_polynomial_basis (x : I → A)
    (hx : ∀ i j k, v.repr (v j * x i) k ∈ D)
    (w : Fin d → MvPolynomial I R)
    (hw : ∀ i, MvPolynomial.aeval x (w i) = v i) (i j k : Fin d) :
    structureCoeff v i j k ∈ D := by
  have h := polynomial_action_coordinates_mem v D x hx (w j) i k
  rwa [hw] at h

end FLT.Mazur.HilbertChart
