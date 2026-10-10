/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFieldChartPresentation
public import FLT.Mazur.WeierstrassNormalizedProjectivePoint
public import FLT.Mazur.WeierstrassIntegralGroupOperations

/-!
# Projective points are field-valued points of the integral cubic

Normalized representatives give a canonical injection from Mathlib's actual
nonsingular projective points to morphisms over the coefficient spectrum.
For unit discriminant it is surjective and therefore gives an equivalence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- Field-valued points of the integral model, with their actual coefficient map. -/
abbrev integralCurveFieldPoint :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ integralCurveOver W

/-- Every projective point is represented by a normalized chart-valued scheme point. -/
theorem exists_projectiveIntegralPoint (P : (W.map (algebraMap R K)).toProjective.Point) :
    ∃ p : integralCurveFieldPoint (K := K) W,
      ∃ (j : Fin 3) (v : Fin 3 → K)
        (hv : (W.map (algebraMap R K)).toProjective.Equation v) (hj : v j = 1),
        (⟦v⟧ : PointClass K) = P.point ∧ p.left = integralChartPoint W j v hv hj := by
  obtain ⟨j, v, hv, hj, he⟩ := exists_normalized_projective (W.map (algebraMap R K)) P
  exact ⟨Over.homMk (integralChartPoint W j v hv hj)
    (integralChartPoint_structure W j v hv hj), j, v, hv, hj, he, rfl⟩

/-- The actual scheme point determined by a nonsingular projective point. -/
def projectiveToIntegral (P : (W.map (algebraMap R K)).toProjective.Point) :
    integralCurveFieldPoint (K := K) W :=
  Classical.choose (exists_projectiveIntegralPoint W P)

/-- The chosen scheme point is computed by every normalized representative. -/
theorem projectiveToIntegral_chart (P : (W.map (algebraMap R K)).toProjective.Point)
    (j : Fin 3) (v : Fin 3 → K)
    (hv : (W.map (algebraMap R K)).toProjective.Equation v) (hj : v j = 1)
    (he : (⟦v⟧ : PointClass K) = P.point) :
    (projectiveToIntegral W P).left = integralChartPoint W j v hv hj := by
  obtain ⟨k, w, hw, hk, hwP, hp⟩ := Classical.choose_spec (exists_projectiveIntegralPoint W P)
  change (projectiveToIntegral W P).left = _ at hp
  rw [hp]
  exact (integralChartPoint_eq_iff_projective W k j w v hw hk hv hj).mpr (hwP.trans he.symm)

/-- The comparison with actual scheme morphisms is injective even without good reduction. -/
theorem projectiveToIntegral_injective : Function.Injective (projectiveToIntegral (K := K) W) := by
  intro P Q h
  obtain ⟨j, v, hv, hj, he⟩ := exists_normalized_projective (W.map (algebraMap R K)) P
  obtain ⟨k, w, hw, hk, hf⟩ := exists_normalized_projective (W.map (algebraMap R K)) Q
  have hc := congrArg Over.Hom.left h
  rw [projectiveToIntegral_chart W P j v hv hj he,
    projectiveToIntegral_chart W Q k w hw hk hf] at hc
  apply Point.ext
  exact he.symm.trans
    (((integralChartPoint_eq_iff_projective W j k v w hv hj hw hk).mp hc).trans hf)

/-- Unit discriminant makes every field-valued scheme point a nonsingular projective point. -/
theorem projectiveToIntegral_surjective (hΔ : IsUnit W.Δ) :
    Function.Surjective (projectiveToIntegral (K := K) W) := by
  intro p
  obtain ⟨j, v, hv, hj, he⟩ := exists_integralChartPoint W p.left p.w
  have hd : (W.map (algebraMap R K)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact (hΔ.map (algebraMap R K)).ne_zero
  let P : (W.map (algebraMap R K)).toProjective.Point :=
    { point := ⟦v⟧
      nonsingular := normalized_equation_nonsingular _ hd j v hv hj }
  refine ⟨P, Over.OverMorphism.ext ?_⟩
  exact (projectiveToIntegral_chart W P j v hv hj rfl).trans he

/-- The field-valued integral model and the classical projective point type agree. -/
def integralProjectivePointEquiv (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R K)).toProjective.Point ≃ integralCurveFieldPoint (K := K) W :=
  Equiv.ofBijective (projectiveToIntegral W)
    ⟨projectiveToIntegral_injective W, projectiveToIntegral_surjective W hΔ⟩

/-- The equivalence is computed on actual normalized coordinates, without changing the base. -/
theorem integralProjectivePointEquiv_chart (hΔ : IsUnit W.Δ)
    (P : (W.map (algebraMap R K)).toProjective.Point) (j : Fin 3) (v : Fin 3 → K)
    (hv : (W.map (algebraMap R K)).toProjective.Equation v) (hj : v j = 1)
    (he : (⟦v⟧ : PointClass K) = P.point) :
    (integralProjectivePointEquiv W hΔ P).left = integralChartPoint W j v hv hj :=
  projectiveToIntegral_chart W P j v hv hj he

end FLT.Mazur.WeierstrassIntegralChart
