/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryNegationEmpty

/-!
# Pulling addition domains back along the affine negation pair

The tensor rings below represent the actual scheme pullbacks. Ordinary domains
become empty, while the reciprocal laws become the zero section on their entire
pullbacks, including infinitesimal points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Regard the affine curve as the point-negation section of its product. -/
@[instance_reducible] def affineNegationInputAlgebra : Algebra (AffineProduct W) (Coordinate W 2) :=
  (affineNegationPair W).toRingHom.toAlgebra

attribute [local instance] affineNegationInputAlgebra

/-- The negation-pair algebra retains the original coefficient action. -/
theorem affineNegationInputTower : IsScalarTower R (AffineProduct W) (Coordinate W 2) :=
  IsScalarTower.of_algebraMap_eq' (affineNegationPair W).comp_algebraMap.symm

attribute [local instance] affineNegationInputTower

/-- Actual tensor pullback of an addition domain along the point-negation pair. -/
def NegationAdditionPullback (i : AdditionChartIndex) :=
  additionChartRing W i ⊗[AffineProduct W] Coordinate W 2

instance (i : AdditionChartIndex) : CommRing (NegationAdditionPullback W i) :=
  inferInstanceAs (CommRing (_ ⊗[AffineProduct W] _))

instance (i : AdditionChartIndex) : Algebra R (NegationAdditionPullback W i) :=
  inferInstanceAs (Algebra R (_ ⊗[AffineProduct W] _))

/-- Restriction from the addition domain. -/
def negationAdditionFirst (i : AdditionChartIndex) :
    additionChartRing W i →ₐ[R] NegationAdditionPullback W i :=
  Algebra.TensorProduct.includeLeft

/-- Restriction from the affine curve on the point-negation section. -/
def negationAdditionSecond (i : AdditionChartIndex) :
    Coordinate W 2 →ₐ[R] NegationAdditionPullback W i :=
  Algebra.TensorProduct.includeRight.restrictScalars R

/-- Both restrictions give the same actual point-negation pair. -/
theorem negationAddition_inputs (i : AdditionChartIndex) :
    (negationAdditionFirst W i).comp (additionChartAlgRestriction W i) =
      (negationAdditionSecond W i).comp (affineNegationPair W) := by
  apply AlgHom.ext
  intro x
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul x

/-- The tensor spectrum represents the categorical pullback. -/
theorem negationAddition_isPullback (i : AdditionChartIndex) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (negationAdditionFirst W i).toRingHom))
      (Spec.map (CommRingCat.ofHom (negationAdditionSecond W i).toRingHom))
      (additionChartInclusion W i)
      (Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)) := by
  apply isPullback_SpecMap_of_isPushout
  simp only [← additionChartAlgRestriction_toRingHom]
  exact CommRingCat.isPushout_tensorProduct (AffineProduct W)
    (additionChartRing W i) (Coordinate W 2)

/-- Each ordinary pullback ring is the zero ring. -/
theorem negationAddition_ordinary_subsingleton (b : Bool) :
    Subsingleton (NegationAdditionPullback W (ordinaryIndex b)) :=
  ordinaryChart_negation_subsingleton W b _ _ (negationAddition_inputs W _)

/-- The actual ordinary-domain pullback has no scheme points. -/
theorem negationAddition_ordinary_isEmpty (b : Bool) :
    IsEmpty (Spec (.of (NegationAdditionPullback W (ordinaryIndex b)))) := by
  let _ := negationAddition_ordinary_subsingleton W b
  exact inferInstanceAs (IsEmpty (PrimeSpectrum (NegationAdditionPullback W (ordinaryIndex b))))

/-- The reciprocal law on its full tensor pullback equals the infinity evaluation. -/
theorem negationAddition_reciprocal (b : Bool) :
    (negationAdditionFirst W (reciprocalIndex b)).comp (reciprocalChartAddition W b) =
      chartInfinityEvaluation W :=
  reciprocalChartAddition_negation W b _ _ (negationAddition_inputs W _)

end FLT.Mazur.WeierstrassIntegralChart
