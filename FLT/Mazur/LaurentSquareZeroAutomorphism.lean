/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentSquareZeroCoordinate
public import FLT.Mazur.LaurentWeightedInverse

/-!
# Full Laurent algebra automorphisms for square-zero vector fields

The polynomial coordinate formula determines a full algebra automorphism.
Composition adds vector fields, its inverse negates them, and every weighted
Laurent function is fixed. These statements retain all negative exponents.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroAutomorphism
open LaurentPolynomial LaurentSquareZeroCoordinate LaurentUnitPoints
variable {R : Type*} [CommRing R] (e : R) (he : e ^ 2 = 0)
local notation "L" => R[T;T⁻¹]

/-- The universal perturbed coordinate, with its explicit inverse unit. -/
def coordinate (q : L) : Lˣ :=
  perturb (C e) (by rw [← map_pow, he, map_zero]) (pointUnit (AlgHom.id R L)) q

/-- Evaluate at the complete perturbed coordinate. -/
def subst (q : L) : L →ₐ[R] L := evalUnit (coordinate e he q)

/-- The forward substitution has the prescribed full positive coordinate. -/
@[simp] theorem subst_T (q : L) : subst e he q (T 1) = T 1 + C e * q := by
  simp only [subst, evalUnit_T, zpow_one, coordinate, perturb_val, pointUnit,
    AlgHom.id_apply]

/-- Square-zero weighting removes the error on every Laurent function. -/
theorem subst_weighted (q z : L) : C e * subst e he q z = C e * z := by
  apply LaurentWeightedInverse.weighted_hom_of_sub_mem e e (by simpa [pow_two] using he)
    (subst e he q) (AlgHom.id R L) ?_ z
  rw [subst_T, AlgHom.id_apply, add_sub_cancel_left,
    Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact ⟨q, rfl⟩

/-- Full substitutions compose by addition, not just at their tangent coefficients. -/
theorem subst_comp (p q : L) :
    (subst e he p).comp (subst e he q) = subst e he (p + q) := by
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change subst e he p (subst e he q (T 1)) = _
  rw [subst_T, map_add, map_mul, show subst e he p (C e) = C e from
    (subst e he p).commutes e, subst_T, subst_weighted, subst_T]
  ring

/-- The zero vector field gives the identity on the entire Laurent algebra. -/
@[simp] theorem subst_zero : subst e he (0 : L) = AlgHom.id R L := by
  apply LaurentNilpotentReparametrization.hom_ext_positive
  simp

/-- The whole Laurent automorphism has the explicit negative-field inverse. -/
def equiv (q : L) : L ≃ₐ[R] L :=
  AlgEquiv.ofAlgHom (subst e he q) (subst e he (-q))
    (by rw [subst_comp, add_neg_cancel, subst_zero])
    (by rw [subst_comp, neg_add_cancel, subst_zero])

/-- The algebra equivalence keeps the complete coordinate formula. -/
@[simp] theorem equiv_T (q : L) : equiv e he q (T 1) = T 1 + C e * q :=
  subst_T e he q

/-- Any original Laurent homomorphism with this coordinate is the constructed automorphism. -/
theorem eq_subst (f : L →ₐ[R] L) (q : L)
    (hf : f (T 1) = T 1 + C e * q) : f = subst e he q :=
  LaurentNilpotentReparametrization.hom_ext_positive (hf.trans (subst_T e he q).symm)

end FLT.Mazur.LaurentSquareZeroAutomorphism
