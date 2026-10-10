/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothOriginalAffine
public import FLT.Mazur.WeierstrassSmoothTripleProduct
public import FLT.Mazur.WeierstrassAffineInputFactorization
public import FLT.Mazur.WeierstrassOrdinaryGlobalDomains
public import FLT.Mazur.WeierstrassReciprocalGlobalDomains

/-!
# Original formula comparisons on the categorical smooth product

An actual presentation of a smooth pair in any original addition chart
computes the smooth sum by that chart's formula, over every coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The smooth product inclusion retains its first input. -/
@[reassoc] theorem smoothFactorsInclusion_fst :
    smoothFactorsInclusion W ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (integralSmoothOpen W).ι := pullback.lift_fst _ _ _

/-- The smooth product inclusion retains its second input. -/
@[reassoc] theorem smoothFactorsInclusion_snd :
    smoothFactorsInclusion W ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (integralSmoothOpen W).ι := pullback.lift_snd _ _ _

/-- Every original addition chart computes the actual smooth sum on common inputs. -/
theorem smoothFactorAddition_chart {X : Scheme.{u}} (p : X ⟶ smoothFactorProduct W)
    (i : AdditionChartIndex) (f : X ⟶ Spec (additionChartRing W i))
    (hf : f ≫ additionGlobalDomain W i = p ≫ smoothFactorsInclusion W) :
    p ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
      f ≫ Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom) ≫
        integralCurveChart W (additionChartOutput i) := by
  have h := smoothCurveAddition_originalPartial W (p ≫ smoothFactorsToProduct W)
    (f ≫ additionChartToDomain W i) (by
      rw [Category.assoc, smoothFactorsToProduct_inclusion, Category.assoc,
        additionChartToDomain_inclusion_assoc]
      exact hf.symm)
  rw [Category.assoc, Category.assoc, additionChartToDomain_addition] at h
  simpa only [smoothFactorAddition, Category.assoc, additionCurveChart,
    additionChartAlgOutput_spec] using h

/-- Ordinary presentations compute smooth addition by the affine formula. -/
theorem smoothFactorAddition_ordinary {X : Scheme.{u}} (p : X ⟶ smoothFactorProduct W)
    (b : Bool) (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (hf : f ≫ ordinaryGlobalDomain W b = p ≫ smoothFactorsInclusion W) :
    p ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) ≫
        integralCurveChart W 2 := by
  have h := smoothFactorAddition_chart W p (ordinaryIndex b) f hf
  cases b <;> exact h

/-- Reciprocal presentations compute smooth addition by the normalized Y-chart formula. -/
theorem smoothFactorAddition_reciprocal {X : Scheme.{u}} (p : X ⟶ smoothFactorProduct W)
    (b : Bool) (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (hf : f ≫ reciprocalGlobalDomain W b = p ≫ smoothFactorsInclusion W) :
    p ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
      f ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom) ≫
        integralCurveChart W 1 := by
  have h := smoothFactorAddition_chart W p (reciprocalIndex b) f hf
  cases b <;> exact h

end FLT.Mazur.WeierstrassIntegralChart
