/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedInfinityOutput
public import FLT.Mazur.WeierstrassInfinityAdditionScheme

/-!
# Actual reversed-input intersections of the infinity addition domain

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
def SwappedInfinityDomain := InfinityAdditionOpen W

instance : CommRing (SwappedInfinityDomain W) :=
  inferInstanceAs (CommRing (InfinityAdditionOpen W))

instance : Algebra R (SwappedInfinityDomain W) :=
  inferInstanceAs (Algebra R (InfinityAdditionOpen W))

instance : Algebra (ChartProduct W 1 1) (SwappedInfinityDomain W) :=
  ((infinityAdditionRestriction W).comp (chartProductSwap W 1 1)).toRingHom.toAlgebra

instance :
    IsScalarTower R (ChartProduct W 1 1) (SwappedInfinityDomain W) :=
  IsScalarTower.of_algebraMap_eq'
    ((infinityAdditionRestriction W).comp (chartProductSwap W 1 1)).comp_algebraMap.symm

/-- Tensor intersection of an original and a reversed addition domain. -/
def SwappedInfinityIntersection :=
  InfinityAdditionOpen W ⊗[ChartProduct W 1 1] SwappedInfinityDomain W

instance : CommRing (SwappedInfinityIntersection W) :=
  inferInstanceAs (CommRing (_ ⊗[ChartProduct W 1 1] _))

instance : Algebra R (SwappedInfinityIntersection W) :=
  inferInstanceAs (Algebra R (_ ⊗[ChartProduct W 1 1] _))

/-- First domain restriction to the reversed-input intersection. -/
def swappedInfinityLeft :
    InfinityAdditionOpen W →ₐ[R] SwappedInfinityIntersection W :=
  Algebra.TensorProduct.includeLeft

/-- Second domain restriction to the reversed-input intersection. -/
def swappedInfinityRight :
    InfinityAdditionOpen W →ₐ[R] SwappedInfinityIntersection W :=
  (Algebra.TensorProduct.includeRight.restrictScalars R :
    SwappedInfinityDomain W →ₐ[R] SwappedInfinityIntersection W)

/-- The tensor identifies the first inputs with the reversed second inputs. -/
theorem swappedInfinity_inputs_twisted :
    (swappedInfinityLeft W).comp (infinityAdditionRestriction W) =
      ((swappedInfinityRight W).comp (infinityAdditionRestriction W)).comp
        (chartProductSwap W 1 1) := by
  apply AlgHom.ext
  intro x
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul x

/-- The second inputs are exactly the reversed first inputs. -/
theorem swappedInfinity_inputs :
    (swappedInfinityRight W).comp (infinityAdditionRestriction W) =
      ((swappedInfinityLeft W).comp (infinityAdditionRestriction W)).comp
        (chartProductSwap W 1 1) := by
  rw [swappedInfinity_inputs_twisted, AlgHom.comp_assoc, chartProductSwap_swap, AlgHom.comp_id]

/-- Scheme involution interchanging the two infinity inputs. -/
def infinityInputSwap : Spec (.of (ChartProduct W 1 1)) ⟶ Spec (.of (ChartProduct W 1 1)) :=
  Spec.map (CommRingCat.ofHom (chartProductSwap W 1 1).toRingHom)

/-- The Y-chart scheme interchange is involutive. -/
@[reassoc] theorem infinityInputSwap_swap : infinityInputSwap W ≫ infinityInputSwap W = 𝟙 _ := by
  rw [infinityInputSwap, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((chartProductSwap W 1 1).comp (chartProductSwap W 1 1)).toRingHom) = _
  rw [chartProductSwap_swap]
  exact Spec.map_id _

/-- The tensor spectrum is the genuine reversed-input pullback. -/
theorem swappedInfinity_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (swappedInfinityLeft W).toRingHom))
      (Spec.map (CommRingCat.ofHom (swappedInfinityRight W).toRingHom))
      (infinityAdditionInclusion W) (infinityAdditionInclusion W ≫ infinityInputSwap W) := by
  simp only [infinityInputSwap, infinityAdditionInclusion,
    ← Spec.map_comp]
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_tensorProduct (ChartProduct W 1 1)
    (InfinityAdditionOpen W) (SwappedInfinityDomain W)

attribute [irreducible] SwappedInfinityIntersection swappedInfinityLeft swappedInfinityRight

/-- Infinity output maps agree on every scheme with reversed Y-chart inputs. -/
theorem infinityAddition_swap_commonScheme {X : Scheme}
    (f g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (hfg : f ≫ infinityAdditionInclusion W =
      g ≫ infinityAdditionInclusion W ≫ infinityInputSwap W) :
    f ≫ infinityAdditionSpec W = g ≫ infinityAdditionSpec W := by
  have he : Spec.map (CommRingCat.ofHom (swappedInfinityLeft W).toRingHom) ≫
        infinityAdditionSpec W =
      Spec.map (CommRingCat.ofHom (swappedInfinityRight W).toRingHom) ≫
        infinityAdditionSpec W := by
    rw [infinityAdditionSpec, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (infinityAdditionChart_swap W _ _ (swappedInfinity_inputs W))
  have hp := swappedInfinity_isPullback W
  have h := congrArg (fun k => hp.lift f g
    (by simpa only [Category.assoc] using hfg) ≫ k) he
  simpa only [← Category.assoc, hp.lift_fst, hp.lift_snd] using h

end FLT.Mazur.WeierstrassIntegralChart
