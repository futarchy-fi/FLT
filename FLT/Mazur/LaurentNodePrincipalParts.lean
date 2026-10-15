/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPositivePart

/-!
# Canonical principal parts of functions on two punctured node branches

Remove the strictly positive terms and the common constant from a Laurent
pair. The resulting linear projection records the two poles and the mismatch
at the node. Its kernel consists exactly of matching polynomial pairs.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.LaurentNodePrincipalParts
open LaurentPolynomial LaurentPositivePart LaurentBoundaryVectorField
variable {R : Type*} [CommRing R]

/-- The boundary-tail operation is linear, including its constant term. -/
def tailLinear : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] where
  toFun := boundaryTail
  map_add' p q := by
    ext d
    by_cases hd : d ≤ 0
    · simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        boundaryTail_coeff_nonpos _ d hd]
    · simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        boundaryTail_coeff_pos _ d (by omega : 0 < d), add_zero]
  map_smul' r p := by
    ext d
    by_cases hd : d ≤ 0
    · simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        boundaryTail_coeff_nonpos _ d hd, RingHom.id_apply]
    · simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        boundaryTail_coeff_pos _ d (by omega : 0 < d), smul_zero, RingHom.id_apply]

/-- The linear map retains the existing boundary-tail function. -/
theorem tailLinear_apply (p : R[T;T⁻¹]) : tailLinear p = boundaryTail p := rfl

/-- Constants are retained by the tail projection. -/
theorem tail_C (r : R) : boundaryTail (C r) = C r := by
  ext d
  by_cases hd : d ≤ 0
  · exact boundaryTail_coeff_nonpos _ d hd
  · rw [boundaryTail_coeff_pos _ d (by omega)]
    change 0 = Finsupp.single 0 r d
    rw [Finsupp.single_eq_of_ne (by omega : d ≠ 0)]

/-- Applying the boundary projection twice does not change the retained coefficients. -/
theorem tail_idempotent (p : R[T;T⁻¹]) : boundaryTail (boundaryTail p) = boundaryTail p := by
  ext d
  by_cases hd : d ≤ 0
  · exact boundaryTail_coeff_nonpos _ d hd
  · rw [boundaryTail_coeff_pos _ d (by omega), boundaryTail_coeff_pos _ d (by omega)]

/-- A canonical representative of the pair modulo matching polynomial node functions. -/
def principalParts : (R[T;T⁻¹] × R[T;T⁻¹]) →ₗ[R] (R[T;T⁻¹] × R[T;T⁻¹]) where
  toFun p := (boundaryTail p.1 - C (p.2.coeff 0), boundaryTail p.2 - C (p.2.coeff 0))
  map_add' p q := by
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, ← tailLinear_apply, map_add,
        AddMonoidAlgebra.coeff_add, Finsupp.add_apply] <;> abel
  map_smul' r p := by
    apply Prod.ext <;>
      simp only [Prod.smul_fst, Prod.smul_snd, ← tailLinear_apply, map_smul,
        AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, RingHom.id_apply,
        smul_sub, smul_eq_mul, map_mul]
    all_goals simp only [smul_eq_C_mul]

/-- The projection is given by the two tails and the original right constant. -/
theorem principalParts_apply (p q : R[T;T⁻¹]) :
    principalParts (p, q) = (boundaryTail p - C (q.coeff 0),
      boundaryTail q - C (q.coeff 0)) := rfl

/-- The representative has zero right constant. -/
theorem principalParts_right_zero (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    (principalParts p).2.coeff 0 = 0 := by
  change (boundaryTail p.2).coeff 0 - (C (p.2.coeff 0)).coeff 0 = 0
  rw [boundaryTail_coeff_nonpos _ 0 le_rfl]
  simp only [C_apply, ite_true, sub_self]

/-- The canonical remainder is an idempotent linear projection. -/
theorem principalParts_idempotent (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    principalParts (principalParts p) = principalParts p := by
  rw [show principalParts (principalParts p) =
    (boundaryTail (principalParts p).1 - C ((principalParts p).2.coeff 0),
      boundaryTail (principalParts p).2 - C ((principalParts p).2.coeff 0)) from rfl,
    principalParts_right_zero, map_zero, sub_zero, sub_zero]
  apply Prod.ext <;>
    change boundaryTail (boundaryTail _ - C _) = _
  all_goals
    rw [← tailLinear_apply, map_sub]
    change boundaryTail (boundaryTail _) - boundaryTail (C _) = _
    rw [tail_idempotent, tail_C]
    rfl

/-- A polynomial's whole tail is precisely its constant term. -/
theorem tail_polynomial (p : R[X]) : boundaryTail p.toLaurent = C (p.coeff 0) := by
  ext d
  rcases lt_trichotomy d 0 with hd | rfl | hd
  · rw [boundaryTail_coeff_nonpos _ d (le_of_lt hd), polynomial_coeff_neg _ d hd]
    change 0 = Finsupp.single 0 _ d
    rw [Finsupp.single_eq_of_ne (ne_of_lt hd)]
  · rw [boundaryTail_coeff_nonpos _ 0 le_rfl, polynomial_coeff_zero, C_apply, ite_eq_left rfl]
  · rw [boundaryTail_coeff_pos _ d hd]
    change 0 = Finsupp.single 0 _ d
    rw [Finsupp.single_eq_of_ne (ne_of_gt hd)]

/-- Vanishing is precisely polynomial extension on both branches with equal node values. -/
theorem principalParts_zero_iff (p q : R[T;T⁻¹]) :
    principalParts (p, q) = 0 ↔
      ∃ a b : R[X], a.toLaurent = p ∧ b.toLaurent = q ∧ a.coeff 0 = b.coeff 0 := by
  constructor
  · intro hp
    have hl : boundaryTail p = C (q.coeff 0) :=
      sub_eq_zero.mp (congrArg Prod.fst hp)
    have hr : boundaryTail q = C (q.coeff 0) :=
      sub_eq_zero.mp (congrArg Prod.snd hp)
    refine ⟨positivePart p + Polynomial.C (q.coeff 0),
      positivePart q + Polynomial.C (q.coeff 0), ?_, ?_, ?_⟩
    · rw [map_add, Polynomial.toLaurent_C]
      exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hl).symm
    · rw [map_add, Polynomial.toLaurent_C]
      exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hr).symm
    · simp only [Polynomial.coeff_add, positivePart_coeff_zero, zero_add]
  · rintro ⟨a, b, rfl, rfl, hab⟩
    rw [principalParts_apply, tail_polynomial, tail_polynomial,
      polynomial_coeff_zero, hab, sub_self]
    rfl

end FLT.Mazur.LaurentNodePrincipalParts
