/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartJacobian
public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# A Jacobian presentation of each normalized cubic chart

The actual chart quotient has a presentation with three variables and the
cubic and normalization relations. Pairing the cubic with a free coordinate
and normalization with its own coordinate gives exactly the free partial as
Jacobian determinant.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j : Fin 3)

/-- Evaluation at universal coordinates is the original quotient map. -/
theorem coord_aeval_eq : aeval (coord W j) = Ideal.Quotient.mkₐ R (relations W j) := by
  ext i
  exact aeval_X (coord W j) i

/-- The original cubic and normalization relations as a two-element family. -/
def chartRelations : Fin 2 → MvPolynomial (Fin 3) R :=
  ![W.toProjective.polynomial, X j - 1]

/-- These are precisely the ideal relations of the original chart. -/
theorem chartRelations_span : Ideal.span (Set.range (chartRelations W j)) = relations W j := by
  simp only [chartRelations, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, relations]

/-- An actual algebra presentation of the normalized chart, with no new relations assumed. -/
def chartPresentation : Algebra.Presentation R (Coordinate W j) (Fin 3) (Fin 2) where
  toGenerators := Algebra.Generators.ofSurjective (coord W j) (by
    rw [coord_aeval_eq]
    exact Ideal.Quotient.mkₐ_surjective R _)
  relation := chartRelations W j
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    change Ideal.span (Set.range (chartRelations W j)) = RingHom.ker (aeval (coord W j))
    rw [chartRelations_span, coord_aeval_eq]
    exact Ideal.mk_ker.symm

/-- The selected free coordinate and normalized coordinate index the two relation derivatives. -/
def chartPreSubmersive (i : Fin 3) (hij : i ≠ j) :
    Algebra.PreSubmersivePresentation R (Coordinate W j) (Fin 3) (Fin 2) where
  toPresentation := chartPresentation W j
  map := ![i, j]
  map_inj := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

/-- The two-by-two determinant is the derivative in the free coordinate. -/
theorem chartPreSubmersive_jacobian (i : Fin 3) (hij : i ≠ j) :
    (chartPreSubmersive W j i hij).jacobian = chartPartial W j i := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change aeval (coord W j)
    (pderiv i W.toProjective.polynomial * pderiv j (X j - 1) -
      pderiv i (X j - 1) * pderiv j W.toProjective.polynomial) = _
  simp [pderiv_X_of_ne hij.symm, chartPartial]

end FLT.Mazur.WeierstrassIntegralChart
