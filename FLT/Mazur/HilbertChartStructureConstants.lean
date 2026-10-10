/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartAlgebra

/-!
# Structure constants of an arbitrary based algebra

Reading multiplication and unit coordinates in an actual basis gives the
summed Hilbert-chart equations. The ring laws are proved from the algebra,
not assumed as part of extra classifying data.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace FLT.Mazur.HilbertChart

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] {d : ℕ}
variable (v : Module.Basis (Fin d) S A)

/-- Coordinates of the actual multiplication in an arbitrary based algebra. -/
def structureCoeff (i j k : Fin d) : S := v.repr (v i * v j) k

/-- Coordinates of the actual unit in an arbitrary based algebra. -/
def structureUnit (k : Fin d) : S := v.repr 1 k

/-- Expand the first factor of a product in the actual basis. -/
theorem repr_mul_basis_left (a : A) (j k : Fin d) :
    v.repr (a * v j) k = ∑ i, v.repr a i * structureCoeff v i j k := by
  conv_lhs => rw [← v.sum_repr a]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, structureCoeff]

/-- Expand the second factor of a product in the actual basis. -/
theorem repr_mul_basis_right (i : Fin d) (a : A) (k : Fin d) :
    v.repr (v i * a) k = ∑ j, v.repr a j * structureCoeff v i j k := by
  conv_lhs => rw [← v.sum_repr a]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, structureCoeff]

/-- The multiplication constants of a commutative algebra are symmetric. -/
theorem structureCoeff_comm (i j k : Fin d) :
    structureCoeff v i j k = structureCoeff v j i k := by
  simp only [structureCoeff, mul_comm]

/-- Associativity in the actual algebra implies the summed coordinate equations. -/
theorem structureCoeff_assoc (i j k l : Fin d) :
    (∑ m, structureCoeff v i j m * structureCoeff v m k l) =
      ∑ m, structureCoeff v j k m * structureCoeff v i m l := by
  calc
    _ = v.repr ((v i * v j) * v k) l := (repr_mul_basis_left v _ k l).symm
    _ = v.repr (v i * (v j * v k)) l := by rw [mul_assoc]
    _ = _ := repr_mul_basis_right v i _ l

/-- The actual unit coordinates satisfy the prescribed left-unit equations. -/
theorem structureUnit_mul (i k : Fin d) :
    (∑ j, structureUnit v j * structureCoeff v j i k) = if i = k then 1 else 0 := by
  calc
    _ = v.repr (1 * v i) k := (repr_mul_basis_left v 1 i k).symm
    _ = _ := by rw [one_mul, Module.Basis.repr_self_apply]

end FLT.Mazur.HilbertChart
