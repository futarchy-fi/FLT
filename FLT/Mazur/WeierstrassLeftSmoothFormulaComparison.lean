/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothOriginalPartial
public import FLT.Mazur.WeierstrassLeftSmoothTripleProduct
public import FLT.Mazur.WeierstrassAffineInputFactorization
public import FLT.Mazur.WeierstrassOrdinaryGlobalDomains
public import FLT.Mazur.WeierstrassReciprocalGlobalDomains

/-!
# Original formula comparisons on the categorical smooth by whole product

An actual presentation of a left smooth pair in any original addition chart
computes the enlarged sum by that chart's formula, over every coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The enlarged product inclusion retains its first input. -/
@[reassoc] theorem leftSmoothFactorsInclusion_fst :
    leftSmoothFactorsInclusion W ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (integralSmoothOpen W).ι := pullback.lift_fst _ _ _

/-- The enlarged product inclusion retains its second input. -/
@[reassoc] theorem leftSmoothFactorsInclusion_snd :
    leftSmoothFactorsInclusion W ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- Every original addition chart computes the actual enlarged sum on common inputs. -/
theorem leftSmoothFactorAddition_chart {X : Scheme.{u}} (p : X ⟶ leftSmoothFactorProduct W)
    (i : AdditionChartIndex) (f : X ⟶ Spec (additionChartRing W i))
    (hf : f ≫ additionGlobalDomain W i = p ≫ leftSmoothFactorsInclusion W) :
    p ≫ leftSmoothFactorAddition W =
      f ≫ Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom) ≫
        integralCurveChart W (additionChartOutput i) := by
  have h := leftSmoothCurveAddition_originalPartial W (p ≫ leftSmoothFactorsToProduct W)
    (f ≫ additionChartToDomain W i) (by
      rw [Category.assoc, leftSmoothFactorsToProduct_inclusion, Category.assoc,
        additionChartToDomain_inclusion_assoc]
      exact hf.symm)
  simp only [Category.assoc, additionChartToDomain_addition] at h
  simpa only [leftSmoothFactorAddition, Category.assoc, additionCurveChart,
    additionChartAlgOutput_spec] using h

/-- Ordinary presentations compute enlarged addition by the affine formula. -/
theorem leftSmoothFactorAddition_ordinary {X : Scheme.{u}} (p : X ⟶ leftSmoothFactorProduct W)
    (b : Bool) (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (hf : f ≫ ordinaryGlobalDomain W b = p ≫ leftSmoothFactorsInclusion W) :
    p ≫ leftSmoothFactorAddition W =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) ≫
        integralCurveChart W 2 := by
  have h := leftSmoothFactorAddition_chart W p (ordinaryIndex b) f hf
  cases b <;> exact h

/-- Reciprocal presentations compute enlarged addition by the normalized Y-chart formula. -/
theorem leftSmoothFactorAddition_reciprocal {X : Scheme.{u}} (p : X ⟶ leftSmoothFactorProduct W)
    (b : Bool) (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (hf : f ≫ reciprocalGlobalDomain W b = p ≫ leftSmoothFactorsInclusion W) :
    p ≫ leftSmoothFactorAddition W =
      f ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom) ≫
        integralCurveChart W 1 := by
  have h := leftSmoothFactorAddition_chart W p (reciprocalIndex b) f hf
  cases b <;> exact h

end FLT.Mazur.WeierstrassIntegralChart
