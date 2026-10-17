/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentSquareZeroAutomorphism
public import FLT.Mazur.LaurentBoundaryCorrectionSplit

/-!
# Factoring a full square-zero Laurent substitution across two boundaries

The two factors preserve opposite boundary origins. The reciprocal factor
includes the derivative sign and inverse-coordinate terms. Their product is
the entire original algebra map, not only its reduction or its tangent.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroAutomorphism
open LaurentPolynomial LaurentSquareZeroCoordinate LaurentUnitPoints
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
variable {R : Type*} [CommRing R] (e : R) (he : e ^ 2 = 0)
local notation "L" => R[T;T⁻¹]

/-- The inverse Laurent generator retains the exact square-zero correction. -/
theorem subst_T_inv (q : L) :
    subst e he q (T (-1)) = T (-1) - C e * q * T (-2) := by
  change (evalUnit (coordinate e he q)) (T (-1)) = _
  rw [evalUnit_T, zpow_neg_one]
  change T (-1) - C e * q * T (-1) ^ 2 = _
  rw [T_pow]
  norm_num

/-- Reciprocal conjugation gives exactly the reciprocal vector field on the whole algebra. -/
theorem subst_reciprocal (q : L) :
    invert.toAlgHom.comp ((subst e he q).comp invert.toAlgHom) =
      subst e he (reciprocalField q) := by
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change invert (subst e he q (invert (T 1))) = _
  rw [invert_T, subst_T_inv, map_sub, map_mul, map_mul, invert_T, invert_C, invert_T,
    subst_T, reciprocalField]
  norm_num
  ring

/-- Every square-zero substitution factors between the two original boundary directions. -/
theorem subst_boundary_factorization (q : L) :
    subst e he q = (subst e he (positivePart q)).comp
      (invert.toAlgHom.comp ((subst e he (reciprocalField (nonpositivePart q))).comp
        invert.toAlgHom)) := by
  rw [subst_reciprocal, reciprocalField_involutive, subst_comp, parts_add]

/-- The factorization also holds for any original map with the specified full coordinate. -/
theorem boundary_factorization_of_coordinate (f : L →ₐ[R] L) (q : L)
    (hf : f (T 1) = T 1 + C e * q) :
    f = (subst e he (positivePart q)).comp
      (invert.toAlgHom.comp ((subst e he (reciprocalField (nonpositivePart q))).comp
        invert.toAlgHom)) := by
  rw [eq_subst e he f q hf, subst_boundary_factorization]

end FLT.Mazur.LaurentSquareZeroAutomorphism
