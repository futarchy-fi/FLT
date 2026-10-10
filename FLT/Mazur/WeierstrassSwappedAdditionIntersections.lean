/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedMixedOutput

/-!
# Actual intersections of affine addition domains with reversed inputs

The second domain carries the input algebra action twisted by tensor interchange.
Its tensor with the first domain represents their genuine scheme pullback.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- A separate copy of an addition domain, with reversed input algebra action. -/
def SwappedAdditionChart (j : AdditionChartIndex) := additionChartRing W j

instance (j : AdditionChartIndex) : CommRing (SwappedAdditionChart W j) :=
  inferInstanceAs (CommRing (additionChartRing W j))

instance (j : AdditionChartIndex) : Algebra R (SwappedAdditionChart W j) :=
  inferInstanceAs (Algebra R (additionChartRing W j))

instance (j : AdditionChartIndex) : Algebra (AffineProduct W) (SwappedAdditionChart W j) :=
  ((additionChartAlgRestriction W j).comp (affineProductSwap W)).toRingHom.toAlgebra

instance (j : AdditionChartIndex) :
    IsScalarTower R (AffineProduct W) (SwappedAdditionChart W j) :=
  IsScalarTower.of_algebraMap_eq'
    ((additionChartAlgRestriction W j).comp (affineProductSwap W)).comp_algebraMap.symm

/-- Tensor intersection of an original and a reversed addition domain. -/
def SwappedAdditionIntersection (i j : AdditionChartIndex) :=
  additionChartRing W i ⊗[AffineProduct W] SwappedAdditionChart W j

instance (i j : AdditionChartIndex) : CommRing (SwappedAdditionIntersection W i j) :=
  inferInstanceAs (CommRing (_ ⊗[AffineProduct W] _))

instance (i j : AdditionChartIndex) : Algebra R (SwappedAdditionIntersection W i j) :=
  inferInstanceAs (Algebra R (_ ⊗[AffineProduct W] _))

/-- First domain restriction to the reversed-input intersection. -/
def swappedAdditionLeft (i j : AdditionChartIndex) :
    additionChartRing W i →ₐ[R] SwappedAdditionIntersection W i j :=
  Algebra.TensorProduct.includeLeft

/-- Second domain restriction to the reversed-input intersection. -/
def swappedAdditionRight (i j : AdditionChartIndex) :
    additionChartRing W j →ₐ[R] SwappedAdditionIntersection W i j :=
  (Algebra.TensorProduct.includeRight.restrictScalars R :
    SwappedAdditionChart W j →ₐ[R] SwappedAdditionIntersection W i j)

/-- The tensor identifies the first inputs with the reversed second inputs. -/
theorem swappedAddition_inputs_twisted (i j : AdditionChartIndex) :
    (swappedAdditionLeft W i j).comp (additionChartAlgRestriction W i) =
      ((swappedAdditionRight W i j).comp (additionChartAlgRestriction W j)).comp
        (affineProductSwap W) := by
  apply AlgHom.ext
  intro x
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul x

/-- The second inputs are exactly the reversed first inputs. -/
theorem swappedAddition_inputs (i j : AdditionChartIndex) :
    (swappedAdditionRight W i j).comp (additionChartAlgRestriction W j) =
      ((swappedAdditionLeft W i j).comp (additionChartAlgRestriction W i)).comp
        (affineProductSwap W) := by
  rw [swappedAddition_inputs_twisted, AlgHom.comp_assoc, affineProductSwap_swap, AlgHom.comp_id]

/-- Scheme involution interchanging the two affine inputs. -/
def affineInputSwap : Spec (.of (AffineProduct W)) ⟶ Spec (.of (AffineProduct W)) :=
  Spec.map (CommRingCat.ofHom (affineProductSwap W).toRingHom)

/-- The affine scheme interchange is involutive. -/
@[reassoc] theorem affineInputSwap_swap : affineInputSwap W ≫ affineInputSwap W = 𝟙 _ := by
  rw [affineInputSwap, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((affineProductSwap W).comp (affineProductSwap W)).toRingHom) = _
  rw [affineProductSwap_swap]
  exact Spec.map_id _

/-- The tensor spectrum is the genuine reversed-input pullback. -/
theorem swappedAddition_isPullback (i j : AdditionChartIndex) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (swappedAdditionLeft W i j).toRingHom))
      (Spec.map (CommRingCat.ofHom (swappedAdditionRight W i j).toRingHom))
      (additionChartInclusion W i) (additionChartInclusion W j ≫ affineInputSwap W) := by
  simp only [affineInputSwap, additionChartInclusion,
    ← additionChartAlgRestriction_toRingHom, ← Spec.map_comp]
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_tensorProduct (AffineProduct W)
    (additionChartRing W i) (SwappedAdditionChart W j)

attribute [irreducible] SwappedAdditionIntersection swappedAdditionLeft swappedAdditionRight

end FLT.Mazur.WeierstrassIntegralChart
