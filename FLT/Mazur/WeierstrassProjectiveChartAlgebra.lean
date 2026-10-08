/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import FLT.Mazur.ProjectiveChartEvaluation

/-!
# The projective chart algebra of the integral cubic

Each normalized cubic chart is a quotient of the corresponding genuine
homogeneous-localization chart of projective two-space. The quotient map
sends coordinate ratios to the universal normalized cubic coordinates.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j : Fin 3)

/-- Evaluation of a projective chart at the universal normalized cubic point. -/
def projectiveChartAlgebra : ProjectiveSpace.chartRing R (Fin 3) j →ₐ[R] Coordinate W j :=
  { ProjectiveSpace.chartEvaluation R (Coordinate W j) 2 (Equiv.swap 0 j) j
      (by simp) (algebraMap R (Coordinate W j)) (coord W j) with
    commutes' := ProjectiveSpace.chartEvaluation_scalar R (Coordinate W j) 2
      (Equiv.swap 0 j) j (by simp) _ _ }

/-- The quotient sends each projective ratio to its actual cubic coordinate. -/
@[simp] theorem projectiveChartAlgebra_coordinate (i : Fin 3) :
    projectiveChartAlgebra W j (ProjectiveSpace.coordinate R (Fin 3) j i) = coord W j i :=
  ProjectiveSpace.chartEvaluation_coordinate R (Coordinate W j) 2 (Equiv.swap 0 j) j
    (by simp) _ _ (coord_self W j) i

/-- Polynomial evaluation at the ratios followed by the quotient is ordinary quotienting. -/
theorem projectiveChartAlgebra_aeval :
    (projectiveChartAlgebra W j).comp
      (aeval (ProjectiveSpace.coordinate R (Fin 3) j)) = Ideal.Quotient.mkₐ R (relations W j) := by
  ext i
  simpa only [AlgHom.comp_apply, aeval_X, coord, Ideal.Quotient.mkₐ_eq_mk] using
    projectiveChartAlgebra_coordinate W j i

/-- Every element of the integral chart comes from its projective ambient chart. -/
theorem projectiveChartAlgebra_surjective : Function.Surjective (projectiveChartAlgebra W j) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨aeval (ProjectiveSpace.coordinate R (Fin 3) j) p, ?_⟩
  exact DFunLike.congr_fun (projectiveChartAlgebra_aeval W j) p

/-- The ambient chart equation is the homogeneous cubic evaluated at its coordinate ratios. -/
def projectiveChartEquation : ProjectiveSpace.chartRing R (Fin 3) j :=
  aeval (ProjectiveSpace.coordinate R (Fin 3) j) W.toProjective.polynomial

/-- The genuine cubic equation vanishes under the chart quotient. -/
@[simp] theorem projectiveChartAlgebra_equation :
    projectiveChartAlgebra W j (projectiveChartEquation W j) = 0 := by
  change ((projectiveChartAlgebra W j).comp
    (aeval (ProjectiveSpace.coordinate R (Fin 3) j))) W.toProjective.polynomial = 0
  rw [projectiveChartAlgebra_aeval]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))

end FLT.Mazur.WeierstrassIntegralChart
