/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeQuotient

/-!
# Arithmetic smoothing equations for polygon node charts

Over any commutative coefficient ring, the chart is the actual finitely
presented algebra with equation xy = t. Its maps represent pairs of
coordinates satisfying that equation, with no reducedness assumption.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R]

/-- The single arithmetic node smoothing equation. -/
def relation (t : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C t

/-- The ideal imposing the actual smoothing equation. -/
def relationIdeal (t : R) : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {relation t}

/-- The ring of the arithmetic node chart at parameter t. -/
abbrev ChartRing (t : R) := MvPolynomial (Fin 2) R ⧸ relationIdeal t

/-- The first branch coordinate on the actual chart. -/
def leftCoordinate (t : R) : ChartRing t := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The second branch coordinate on the actual chart. -/
def rightCoordinate (t : R) : ChartRing t := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The original coordinates satisfy the smoothing equation in the quotient ring. -/
theorem coordinate_relation (t : R) :
    leftCoordinate t * rightCoordinate t = algebraMap R (ChartRing t) t := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (relationIdeal t) (relation t) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

instance chartRing_finitePresentation (t : R) : Algebra.FinitePresentation R (ChartRing t) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluation at any actual pair of coordinates solving xy = t. -/
def evaluate (t : R) (x y : S) (h : x * y = algebraMap R S t) : ChartRing t →ₐ[R] S :=
  Ideal.Quotient.liftₐ (relationIdeal t) (MvPolynomial.aeval ![x, y]) (by
    change relationIdeal t ≤ RingHom.ker (MvPolynomial.aeval ![x, y]).toRingHom
    rw [relationIdeal, Ideal.span_le, Set.singleton_subset_iff]
    change MvPolynomial.aeval ![x, y] (relation t) = 0
    simp only [relation, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, h, sub_self])

/-- Evaluation retains the first branch coordinate. -/
@[simp] theorem evaluate_left (t : R) (x y : S) (h : x * y = algebraMap R S t) :
    evaluate t x y h (leftCoordinate t) = x := by
  change MvPolynomial.aeval ![x, y] (MvPolynomial.X (0 : Fin 2)) = x
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero]

/-- Evaluation retains the second branch coordinate. -/
@[simp] theorem evaluate_right (t : R) (x y : S) (h : x * y = algebraMap R S t) :
    evaluate t x y h (rightCoordinate t) = y := by
  change MvPolynomial.aeval ![x, y] (MvPolynomial.X (1 : Fin 2)) = y
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- Two branch values determine a map from the whole arithmetic chart. -/
@[ext] theorem chartRing_hom_ext (t : R) (f g : ChartRing t →ₐ[R] S)
    (hx : f (leftCoordinate t) = g (leftCoordinate t))
    (hy : f (rightCoordinate t) = g (rightCoordinate t)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- The chart represents precisely the pairs satisfying its original arithmetic equation. -/
def coordinateEquiv (t : R) :
    (ChartRing t →ₐ[R] S) ≃ {p : S × S // p.1 * p.2 = algebraMap R S t} where
  toFun f := ⟨(f (leftCoordinate t), f (rightCoordinate t)), by
    rw [← map_mul, coordinate_relation, AlgHom.commutes]⟩
  invFun p := evaluate t p.val.1 p.val.2 p.property
  left_inv f := chartRing_hom_ext t _ _ (evaluate_left ..) (evaluate_right ..)
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (evaluate_left ..) (evaluate_right ..)

/-- The represented coordinates commute with every map of test algebras. -/
theorem coordinateEquiv_natural {U : Type*} [CommRing U] [Algebra R U]
    (t : R) (f : ChartRing t →ₐ[R] S) (g : S →ₐ[R] U) :
    (coordinateEquiv t (g.comp f)).val =
      (g (coordinateEquiv t f).val.1, g (coordinateEquiv t f).val.2) := rfl

end FLT.Mazur.PolygonSmoothing
