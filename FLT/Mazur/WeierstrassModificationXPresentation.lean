/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFlat
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# A three-variable presentation of the actual x-direction chart

Retaining t, v, x gives the two equations t*x=s and x=F(t,v).
Eliminating x recovers the existing equation algebra by an explicit algebra
isomorphism. This presentation retains the horizontal variable used to
saturate the total-transform equation.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The recovered horizontal coordinate as a polynomial in t and v. -/
def horizontalPolynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + (C W.a₁ + C b3 * X 0) * X 1 -
    (C W.a₂ + C b4 * X 0 + C b6 * X 0 ^ 2)

/-- The incidence polynomial retaining the original horizontal variable. -/
def incidencePolynomial : MvPolynomial (Fin 3) R := X 0 * X 2 - C s

/-- The divided original cubic in the three-variable presentation. -/
def strictPolynomial : MvPolynomial (Fin 3) R := X 2 - horizontalPolynomial W b3 b4 b6

/-- The two explicit strict-transform relations. -/
def strictRelations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {incidencePolynomial s, strictPolynomial W b3 b4 b6}

/-- The quotient retaining the original horizontal coordinate. -/
abbrev StrictCoordinate := MvPolynomial (Fin 3) R ⧸ strictRelations W s b3 b4 b6

/-- The retained universal coordinates t, v, x. -/
def strictCoord (i : Fin 3) : StrictCoordinate W s b3 b4 b6 := Ideal.Quotient.mk _ (X i)

/-- Evaluation at the retained coordinates is the quotient map. -/
theorem strictCoord_aeval : aeval (strictCoord W s b3 b4 b6) =
    Ideal.Quotient.mkₐ R (strictRelations W s b3 b4 b6) := by
  ext i
  exact aeval_X _ i

/-- The incidence equation holds in the explicit presentation. -/
theorem strictCoord_incidence : strictCoord W s b3 b4 b6 0 * strictCoord W s b3 b4 b6 2 =
    algebraMap R _ s := by
  have h : aeval (strictCoord W s b3 b4 b6) (incidencePolynomial s) = 0 := by
    rw [strictCoord_aeval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  simpa only [incidencePolynomial, map_sub, map_mul, sub_eq_zero, aeval_X, aeval_C] using h

/-- The retained horizontal coordinate equals the recovered polynomial expression. -/
theorem strictCoord_horizontal : strictCoord W s b3 b4 b6 2 =
    strictCoord W s b3 b4 b6 1 ^ 2 +
      (algebraMap R _ W.a₁ + algebraMap R _ b3 * strictCoord W s b3 b4 b6 0) *
        strictCoord W s b3 b4 b6 1 -
      (algebraMap R _ W.a₂ + algebraMap R _ b4 * strictCoord W s b3 b4 b6 0 +
        algebraMap R _ b6 * strictCoord W s b3 b4 b6 0 ^ 2) := by
  have h : aeval (strictCoord W s b3 b4 b6) (strictPolynomial W b3 b4 b6) = 0 := by
    rw [strictCoord_aeval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  simpa only [strictPolynomial, horizontalPolynomial, map_sub, map_add, map_mul, map_pow,
    sub_eq_zero, aeval_X, aeval_C] using h

/-- Reintroducing the eliminated coordinate gives a map to the strict presentation. -/
def toStrictCoordinate : Coordinate W s b3 b4 b6 →ₐ[R] StrictCoordinate W s b3 b4 b6 :=
  evaluation W s b3 b4 b6 (strictCoord W s b3 b4 b6 0) (strictCoord W s b3 b4 b6 1) (by
    rw [← strictCoord_horizontal]
    exact strictCoord_incidence W s b3 b4 b6)

/-- Eliminating the retained horizontal coordinate gives the original equation algebra. -/
def fromStrictCoordinate : StrictCoordinate W s b3 b4 b6 →ₐ[R] Coordinate W s b3 b4 b6 :=
  Ideal.Quotient.liftₐ _ (aeval ![t W s b3 b4 b6, v W s b3 b4 b6, x W s b3 b4 b6]) (by
    change strictRelations W s b3 b4 b6 ≤
      RingHom.ker (aeval ![t W s b3 b4 b6, v W s b3 b4 b6, x W s b3 b4 b6]).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · change aeval _ (incidencePolynomial s) = 0
      simp only [incidencePolynomial, map_sub, map_mul, aeval_X, aeval_C,
        Matrix.cons_val_zero, Matrix.cons_val_two, sub_eq_zero]
      exact incidence W s b3 b4 b6
    · have hp' := Set.mem_singleton_iff.mp hp
      subst p
      change aeval _ (strictPolynomial W b3 b4 b6) = 0
      simp only [strictPolynomial, horizontalPolynomial, map_sub, map_add, map_mul, map_pow,
        aeval_X, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      change x W s b3 b4 b6 - x W s b3 b4 b6 = 0
      exact sub_self _)

/-- Elimination preserves each retained coordinate. -/
@[simp] theorem fromStrictCoordinate_coord (i : Fin 3) :
    fromStrictCoordinate W s b3 b4 b6 (strictCoord W s b3 b4 b6 i) =
      ![t W s b3 b4 b6, v W s b3 b4 b6, x W s b3 b4 b6] i := aeval_X _ i

/-- Reintroducing the horizontal coordinate preserves the recovered original x. -/
@[simp] theorem toStrictCoordinate_x :
    toStrictCoordinate W s b3 b4 b6 (x W s b3 b4 b6) = strictCoord W s b3 b4 b6 2 := by
  simp only [x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes,
    toStrictCoordinate, evaluation_t, evaluation_v]
  exact (strictCoord_horizontal W s b3 b4 b6).symm

/-- The explicit strict presentation is the actual equation chart, by inverse substitutions. -/
def strictCoordinateEquiv : StrictCoordinate W s b3 b4 b6 ≃ₐ[R] Coordinate W s b3 b4 b6 := by
  apply AlgEquiv.ofAlgHom (fromStrictCoordinate W s b3 b4 b6) (toStrictCoordinate W s b3 b4 b6)
  · apply hom_ext
    · change fromStrictCoordinate W s b3 b4 b6
        (toStrictCoordinate W s b3 b4 b6 (t W s b3 b4 b6)) = _
      rw [toStrictCoordinate, evaluation_t, fromStrictCoordinate_coord]
      rfl
    · change fromStrictCoordinate W s b3 b4 b6
        (toStrictCoordinate W s b3 b4 b6 (v W s b3 b4 b6)) = _
      rw [toStrictCoordinate, evaluation_v, fromStrictCoordinate_coord]
      rfl
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change toStrictCoordinate W s b3 b4 b6
      (fromStrictCoordinate W s b3 b4 b6 (strictCoord W s b3 b4 b6 i)) =
        strictCoord W s b3 b4 b6 i
    rw [fromStrictCoordinate_coord]
    fin_cases i
    · exact evaluation_t _ _ _ _ _ _ _ _
    · exact evaluation_v _ _ _ _ _ _ _ _
    · exact toStrictCoordinate_x W s b3 b4 b6

end FLT.Mazur.WeierstrassModificationX
