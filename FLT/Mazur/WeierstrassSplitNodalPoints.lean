/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalTorus
public import FLT.Mazur.WeierstrassProjectivePointComparison

/-!
# All nonsingular split nodal points belong to the multiplicative chart

The Y coordinate of a nonsingular point is nonzero. Normalizing it to one
identifies the actual projective point type with algebra maps from the
original infinity chart, without a discriminant hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] (a : Rˣ)

/-- A nonsingular point of a split nodal cubic has nonzero Y coordinate. -/
theorem splitNodalPoint_y_ne_zero (v : Fin 3 → K)
    (hv : ((splitNodalEquation a).map (algebraMap R K)).toProjective.Nonsingular v) :
    v 1 ≠ 0 := by
  intro hy
  have he := hv.1
  rw [equation_iff] at he
  have hx : v 0 = 0 := by
    simpa [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective, hy] using he
  rw [nonsingular_iff] at hv
  simpa [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective, hx, hy] using hv.2

/-- Every actual nonsingular nodal point has a representative in the original Y chart. -/
theorem exists_splitNodalYPoint
    (P : ((splitNodalEquation a).map (algebraMap R K)).toProjective.Point) :
    ∃ (v : Fin 3 → K) (_hv :
      ((splitNodalEquation a).map (algebraMap R K)).toProjective.Equation v) (_hy : v 1 = 1),
      (⟦v⟧ : PointClass K) = P.point := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep P.point
  have hn : ((splitNodalEquation a).map (algebraMap R K)).toProjective.Nonsingular v := by
    have h := P.nonsingular
    rw [← hv] at h
    exact h
  have hy := splitNodalPoint_y_ne_zero a v hn
  have hu := isUnit_iff_ne_zero.mpr (inv_ne_zero hy)
  refine ⟨(v 1)⁻¹ • v, (equation_smul v hu).mpr hn.1, inv_mul_cancel₀ hy, ?_⟩
  exact (smul_eq v hu).trans hv

/-- Every algebra point of the original infinity chart is nonsingular. -/
theorem splitNodalChartPoint_nonsingular (f : Coordinate (splitNodalEquation a) 1 →ₐ[R] K) :
    ((splitNodalEquation a).map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ coord (splitNodalEquation a) 1) := by
  refine ⟨projective_equation_of_hom _ _ f, Or.inr (Or.inr ?_)⟩
  have hu := ((splitNodalTangentUnit a).isUnit.map f.toRingHom).ne_zero
  change f (1 + algebraMap R _ a * coord (splitNodalEquation a) 1 0) ≠ 0 at hu
  rw [eval_polynomialZ]
  simpa [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective,
    Function.comp_def] using hu

/-- A nodal infinity-chart algebra point gives an actual nonsingular projective point. -/
def splitNodalChartProjective (f : Coordinate (splitNodalEquation a) 1 →ₐ[R] K) :
    ((splitNodalEquation a).map (algebraMap R K)).toProjective.Point where
  point := ⟦f ∘ coord (splitNodalEquation a) 1⟧
  nonsingular := splitNodalChartPoint_nonsingular a f

/-- Normalization makes chart coordinates uniquely determined by the projective point. -/
theorem splitNodalChartProjective_injective :
    Function.Injective (splitNodalChartProjective (K := K) a) := by
  intro f g he
  have h := congrArg Point.point he
  have hc := (normalized_projective_eq_iff 1 1
    (f ∘ coord (splitNodalEquation a) 1) (g ∘ coord (splitNodalEquation a) 1)
    (by simp) (by simp)).mp h
  apply hom_ext
  intro i
  simpa using hc i

/-- Every nonsingular nodal point comes from the original infinity chart. -/
theorem splitNodalChartProjective_surjective :
    Function.Surjective (splitNodalChartProjective (K := K) a) := by
  intro P
  obtain ⟨v, hv, hy, he⟩ := exists_splitNodalYPoint a P
  refine ⟨evaluation (splitNodalEquation a) 1 v hv hy, Point.ext ?_⟩
  change (⟦_⟧ : PointClass K) = P.point
  have h : evaluation (splitNodalEquation a) 1 v hv hy ∘
      coord (splitNodalEquation a) 1 = v := funext (evaluation_coord _ _ _ _ _)
  rw [h]
  exact he

/-- The actual projective point type is exactly the algebra points of the multiplicative chart. -/
def splitNodalChartPointEquiv : (Coordinate (splitNodalEquation a) 1 →ₐ[R] K) ≃
    ((splitNodalEquation a).map (algebraMap R K)).toProjective.Point :=
  Equiv.ofBijective (splitNodalChartProjective a)
    ⟨splitNodalChartProjective_injective a, splitNodalChartProjective_surjective a⟩

/-- The point equivalence agrees with the original glued-model comparison. -/
theorem splitNodalChartProjective_toIntegral
    (f : Coordinate (splitNodalEquation a) 1 →ₐ[R] K) :
    (projectiveToIntegral (splitNodalEquation a) (splitNodalChartProjective a f)).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart (splitNodalEquation a) 1 := by
  rw [projectiveToIntegral_chart _ _ 1 _ (projective_equation_of_hom _ _ f) (by simp) rfl]
  unfold integralChartPoint
  congr 2
  apply CommRingCat.hom_ext
  apply congrArg AlgHom.toRingHom
  apply hom_ext
  intro i
  exact evaluation_coord _ _ _ _ _ i

end FLT.Mazur.WeierstrassIntegralChart
