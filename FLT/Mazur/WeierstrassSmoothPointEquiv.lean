/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveRelativeSmoothCriterion

/-!
# Classical points are precisely field points of the actual smooth scheme

The inverse comparison uses the actual field-point chart presentation and
relative smoothness criterion. It works for singular as well as smooth
coefficient cubics and does not require an invertible discriminant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] (W : WeierstrassCurve R)

/-- Field-valued points of the full relative smooth open, over the original coefficient map. -/
abbrev smoothCurveFieldPoint :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
    Over.mk (integralSmoothStructure W)

/-- The canonical smooth-point comparison as a morphism over the coefficient spectrum. -/
def projectiveToSmoothOver (P : (W.map (algebraMap R K)).toProjective.Point) :
    smoothCurveFieldPoint (K := K) W :=
  Over.homMk (projectiveToSmooth W P) (projectiveToSmooth_structure W P)

/-- The actual smooth comparison loses no classical point. -/
theorem projectiveToSmoothOver_injective :
    Function.Injective (projectiveToSmoothOver (K := K) W) := by
  intro P Q h
  apply projectiveToIntegral_injective W
  apply Over.OverMorphism.ext
  have he := congrArg (fun s : smoothCurveFieldPoint (K := K) W =>
    s.left ≫ (integralSmoothOpen W).ι) h
  exact (projectiveToSmooth_inclusion W P).symm.trans
    (he.trans (projectiveToSmooth_inclusion W Q))

/-- Every actual smooth scheme point comes from a classical nonsingular projective point. -/
theorem projectiveToSmoothOver_surjective :
    Function.Surjective (projectiveToSmoothOver (K := K) W) := by
  intro p
  obtain ⟨j, v, hv, hj, he⟩ := exists_integralChartPoint W
    (p.left ≫ (integralSmoothOpen W).ι) ((Category.assoc _ _ _).trans p.w)
  have hs : Set.range (integralChartPoint W j v hv hj) ⊆ integralSmoothOpen W := by
    rw [he]
    rintro _ ⟨x, rfl⟩
    exact (p.left x).property
  have hn := chartFieldPoint_nonsingular_of_smooth W j (evaluation W j v hv hj) hs
  have hn' : (W.map (algebraMap R K)).toProjective.Nonsingular v := by
    have hc : (evaluation W j v hv hj) ∘ coord W j = v := by
      funext i
      exact evaluation_coord _ _ _ _ _ _
    rwa [hc] at hn
  let P : (W.map (algebraMap R K)).toProjective.Point :=
    { point := ⟦v⟧
      nonsingular := hn' }
  refine ⟨P, Over.OverMorphism.ext ?_⟩
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  exact (projectiveToSmooth_inclusion W P).trans
    ((projectiveToIntegral_chart W P j v hv hj rfl).trans he)

/-- Nonsingular projective points and actual smooth field points agree without good reduction. -/
def smoothProjectivePointEquiv :
    (W.map (algebraMap R K)).toProjective.Point ≃ smoothCurveFieldPoint (K := K) W :=
  Equiv.ofBijective (projectiveToSmoothOver W)
    ⟨projectiveToSmoothOver_injective W, projectiveToSmoothOver_surjective W⟩

/-- The equivalence retains the original morphism into the cubic. -/
theorem smoothProjectivePointEquiv_inclusion
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    (smoothProjectivePointEquiv W P).left ≫ (integralSmoothOpen W).ι =
      (projectiveToIntegral W P).left := projectiveToSmooth_inclusion W P

end FLT.Mazur.WeierstrassIntegralChart
