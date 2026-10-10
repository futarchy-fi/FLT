/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothPointEquiv
public import FLT.Mazur.WeierstrassOrdinaryPointComparison
public import FLT.Mazur.WeierstrassSmoothFormulaComparison
public import FLT.Mazur.WeierstrassSmoothGroupOperations

/-!
# Ordinary field-point addition on the actual smooth group

The smooth pairing has the original classical inputs. The actual ordinary
chart formula therefore identifies its geometric output with the classical
sum, without an invertible-discriminant assumption on the coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open WeierstrassCurve WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] (W : WeierstrassCurve R)

/-- Pairing classical smooth points retains their original pair in the full cubic. -/
theorem smoothFieldPoint_pair_inclusion
    (P Q : (W.map (algebraMap R K)).toProjective.Point) :
    (lift (projectiveToSmoothOver W P) (projectiveToSmoothOver W Q)).left ≫
        smoothFactorsInclusion W =
      (lift (projectiveToIntegral W P) (projectiveToIntegral W Q)).left := by
  have hs₁ : (lift (projectiveToSmoothOver W P) (projectiveToSmoothOver W Q)).left ≫
      pullback.fst (integralSmoothStructure W) (integralSmoothStructure W) =
        projectiveToSmooth W P := pullback.lift_fst _ _
          ((projectiveToSmoothOver W P).w.trans (projectiveToSmoothOver W Q).w.symm)
  have hs₂ : (lift (projectiveToSmoothOver W P) (projectiveToSmoothOver W Q)).left ≫
      pullback.snd (integralSmoothStructure W) (integralSmoothStructure W) =
        projectiveToSmooth W Q := pullback.lift_snd _ _
          ((projectiveToSmoothOver W P).w.trans (projectiveToSmoothOver W Q).w.symm)
  have hi₁ : (lift (projectiveToIntegral W P) (projectiveToIntegral W Q)).left ≫
      pullback.fst (integralCurveStructure W) (integralCurveStructure W) =
        (projectiveToIntegral W P).left := pullback.lift_fst _ _
          ((projectiveToIntegral W P).w.trans (projectiveToIntegral W Q).w.symm)
  have hi₂ : (lift (projectiveToIntegral W P) (projectiveToIntegral W Q)).left ≫
      pullback.snd (integralCurveStructure W) (integralCurveStructure W) =
        (projectiveToIntegral W Q).left := pullback.lift_snd _ _
          ((projectiveToIntegral W P).w.trans (projectiveToIntegral W Q).w.symm)
  apply pullback.hom_ext
  · rw [Category.assoc, smoothFactorsInclusion_fst, ← Category.assoc, hs₁, hi₁]
    exact projectiveToSmooth_inclusion W P
  · rw [Category.assoc, smoothFactorsInclusion_snd, ← Category.assoc, hs₂, hi₂]
    exact projectiveToSmooth_inclusion W Q

/-- An ordinary chart computes the classical sum in the full relative smooth group. -/
theorem projectiveToSmoothOver_add_ordinary (b : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] K)
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputLeft W b (coord W 2 0))) (f (ordinaryInputLeft W b (coord W 2 1))))
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputRight W b (coord W 2 0))) (f (ordinaryInputRight W b (coord W 2 1)))) :
    projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂)) =
      lift (projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₁)))
        (projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₂))) ≫
          integralSmoothOverAddition W := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  change projectiveToSmooth W _ ≫ _ = (_ ≫ smoothFactorAddition W) ≫ _
  rw [projectiveToSmooth_inclusion, Category.assoc]
  rw [smoothFactorAddition_ordinary W _ b (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    rw [smoothFieldPoint_pair_inclusion]
    exact ordinaryFieldPoint_pair W b f h₁ h₂)]
  rw [← Category.assoc, ← Spec.map_comp]
  rw [projectiveToIntegral_chart W _ 2 _
    (chartAlgHom_equation W 2 (f.comp (ordinaryChartAddition W b))) (by simp)
    (ordinarySpecialization_projective_sum W b f h₁ h₂).symm,
    integralChartPoint, evaluation_chartAlgHom]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
