/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonScalingNaturality
public import FLT.Mazur.LaurentUnitPoints

/-!
# Coefficient formulas and unit evaluation for Laurent coefficient change

The geometric coefficient map is exactly the coefficientwise ring map.
Evaluation at one commutes with any coefficient homomorphism.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentCoefficientEvaluation
open PolygonScalingNaturality
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The specified Laurent coefficient substitution acts coefficientwise. -/
theorem coeffMap_eq (f : R →+* S) : coeffMap f = AddMonoidAlgebra.mapRingHom ℤ f := by
  apply ringHom_ext
  · intro r
    rw [coeffMap_C]
    exact (AddMonoidAlgebra.mapRingHom_single f 0 r).symm
  · rw [coeffMap_T_one]
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]
  · rw [coeffMap_T_neg_one]
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]

/-- Every Laurent coefficient is preserved by the prescribed coefficient homomorphism. -/
theorem coeffMap_coeff (f : R →+* S) (p : R[T;T⁻¹]) (d : ℤ) :
    (coeffMap f p).coeff d = f (p.coeff d) := by
  rw [coeffMap_eq, AddMonoidAlgebra.coeff_mapRingHom]

/-- Coefficient change preserves every integral Laurent power, including negative powers. -/
theorem coeffMap_T (f : R →+* S) (d : ℤ) :
    coeffMap f (LaurentPolynomial.T d) = LaurentPolynomial.T d := by
  rw [coeffMap_eq]
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]

/-- Evaluation at the unit section commutes with every coefficient change. -/
theorem evalOne_natural (f : R →+* S) :
    (LaurentUnitPoints.evalUnit (R := S) (1 : Sˣ)).toRingHom.comp (coeffMap f) =
      f.comp (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom := by
  apply ringHom_ext <;> simp [LaurentUnitPoints.evalUnit]

end FLT.Mazur.LaurentCoefficientEvaluation
