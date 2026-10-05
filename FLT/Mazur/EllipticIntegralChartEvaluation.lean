/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticIntegralChartCover
public import FLT.Mazur.WeierstrassIntegralChart

/-!
# Actual elliptic points evaluated on integral charts

Normalized primitive lifts define integral chart evaluations. Extending scalars
recovers their generic coordinates; reducing the evaluation gives exactly the
previously constructed projective reduction, without a smoothness assumption.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve.Projective WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {P : (W.map (algebraMap A K)).toProjective.Point}

/-- A normalized primitive lift gives an integral point of the actual chart algebra. -/
def PrimitiveLift.chartEvaluation (v : PrimitiveLift A P.point)
    (j : Fin 3) (hj : v.coords j = 1) : Coordinate W j →ₐ[A] A :=
  evaluation W j v.coords (by
    simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id] using v.equation A W) hj

/-- Integral chart coordinates evaluate to the primitive coordinates. -/
@[simp] theorem PrimitiveLift.chartEvaluation_coord (v : PrimitiveLift A P.point)
    (j : Fin 3) (hj : v.coords j = 1) (i : Fin 3) :
    v.chartEvaluation A W j hj (coord W j i) = v.coords i :=
  evaluation_coord W j _ _ _ i

/-- Extending the integral evaluation recovers the generic normalized point. -/
theorem PrimitiveLift.chartEvaluation_generic (v : PrimitiveLift A P.point)
    (j : Fin 3) (hj : v.coords j = 1) :
    (Algebra.ofId A K).comp (v.chartEvaluation A W j hj) =
      evaluation W j (fun i => (v.coords i : K))
        ((v.equation A W).map (algebraMap A K)) (by simp only [hj, OneMemClass.coe_one]) := by
  apply hom_ext
  intro i
  rw [AlgHom.comp_apply, PrimitiveLift.chartEvaluation_coord]
  exact (WeierstrassIntegralChart.evaluation_coord W j
    (fun i => (v.coords i : K)) _ _ i).symm

/-- Reduction of the integral evaluation is evaluation on the reduced cubic. -/
theorem PrimitiveLift.chartEvaluation_residue (v : PrimitiveLift A P.point)
    (j : Fin 3) (hj : v.coords j = 1) :
    (Algebra.ofId A (ResidueField A)).comp (v.chartEvaluation A W j hj) =
      evaluation W j (residue A ∘ v.coords) (v.residue_equation A W)
        (by simp only [Function.comp_apply, hj, map_one]) := by
  apply hom_ext
  intro i
  rw [AlgHom.comp_apply, PrimitiveLift.chartEvaluation_coord]
  exact (WeierstrassIntegralChart.evaluation_coord W j
    (residue A ∘ v.coords) _ _ i).symm

/-- The residue evaluation represents actual projective point reduction. -/
theorem PrimitiveLift.chartEvaluation_reduction (v : PrimitiveLift A P.point)
    (j : Fin 3) (hj : v.coords j = 1) :
    (⟦fun i => residue A (v.chartEvaluation A W j hj (coord W j i))⟧ :
      PointClass (ResidueField A)) = projectiveReduction A W P := by
  simp only [PrimitiveLift.chartEvaluation_coord]
  exact (projectiveReduction_eq A W P v).symm

/-- Normalized coordinates are independent of the primitive representative. -/
theorem PrimitiveLift.normalized_coords_eq (v w : PrimitiveLift A P.point)
    (j : Fin 3) (hv : v.coords j = 1) (hw : w.coords j = 1) : v.coords = w.coords := by
  obtain ⟨u, hu⟩ := primitive_equiv_of_generic_equiv A v.primitive w.primitive
    (Quotient.exact (v.represents.trans w.represents.symm))
  have hj := congrFun hu j
  have hu1 : (u : A) = 1 := by
    simpa only [Units.smul_def, Pi.smul_apply, smul_eq_mul, hv, hw, mul_one] using hj
  simpa only [Units.smul_def, hu1, one_smul] using hu.symm

/-- Consequently the chart point itself is independent of the chosen primitive lift. -/
theorem PrimitiveLift.chartEvaluation_eq (v w : PrimitiveLift A P.point)
    (j : Fin 3) (hv : v.coords j = 1) (hw : w.coords j = 1) :
    v.chartEvaluation A W j hv = w.chartEvaluation A W j hw := by
  apply hom_ext
  intro i
  simp only [PrimitiveLift.chartEvaluation_coord]
  exact congrFun (v.normalized_coords_eq A W w j hv hw) i

end FLT.Mazur
