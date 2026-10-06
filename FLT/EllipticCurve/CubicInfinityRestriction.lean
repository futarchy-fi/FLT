/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityChartAddition

/-! # Restriction of infinity-chart addition under input chart changes -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem infinityChartAddition_after_finite [W.IsElliptic] (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S] (f : InfinityFiniteRing W b →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (f.comp (infinityFiniteRestriction W b)).toRingHom) ≫
        infinityChartAddition W =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityFiniteAddition W b := by
  change Spec.map (CommRingCat.ofHom (infinityFiniteRestriction W b).toRingHom ≫
    CommRingCat.ofHom f.toRingHom) ≫ infinityChartAddition W = _
  rw [Spec.map_comp, Category.assoc]
  exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom f.toRingHom) ≫ k)
    (infinityChartAddition_restrict W (some b))

/-- Inputs when one infinity-chart point lies on the overlap. -/
def infinityOverlapInputs (b : Bool) {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    ChartPairRing W true true →ₐ[R] S :=
  if b then Algebra.TensorProduct.productMap v
    (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)))
  else Algebra.TensorProduct.productMap
    (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) v

theorem infinityOverlapInputs_selected (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    (infinityOverlapInputs W b a v).comp (infinityPairInput W b) =
      a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)) := by
  cases b
  · exact Algebra.TensorProduct.productMap_left _ _
  · exact Algebra.TensorProduct.productMap_right _ _

theorem infinityOverlapInputs_other (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    (infinityOverlapInputs W b a v).comp (infinityPairInput W (!b)) = v := by
  cases b
  · exact Algebra.TensorProduct.productMap_right _ _
  · exact Algebra.TensorProduct.productMap_left _ _

/-- The overlap-valued pair factors through its selected finite-input domain. -/
def infinityOverlapLift (b : Bool) {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    InfinityFiniteRing W b →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (infinityPairCoord W b 1)
    (f := infinityOverlapInputs W b a v)
    (isUnit_iff_exists_inv.mpr ⟨a (inv W true), by
      have h := DFunLike.congr_fun (infinityOverlapInputs_selected W b a v) (coord W true 1)
      change infinityOverlapInputs W b a v (infinityPairCoord W b 1) = a (loc W true 1) at h
      rw [h, ← map_mul, loc_mul_inv, map_one]⟩)

theorem infinityOverlapLift_restriction (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    (infinityOverlapLift W b a v).comp (infinityFiniteRestriction W b) =
      infinityOverlapInputs W b a v := by
  apply AlgHom.ext
  intro x
  simp [infinityOverlapLift, infinityFiniteRestriction]

theorem infinityOverlapLift_overlap (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    (infinityOverlapLift W b a v).comp (infinityFiniteOverlap W b) = a := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coord W true 1))
  apply AlgHom.ext
  intro x
  change infinityOverlapLift W b a v
    (infinityFiniteOverlap W b (algebraMap (Ring W true) (Overlap W true) x)) = _
  rw [infinityFiniteOverlap_restriction]
  have h := congrArg (fun k : ChartPairRing W true true →ₐ[R] S ↦
    k.comp (infinityPairInput W b)) (infinityOverlapLift_restriction W b a v)
  rw [infinityOverlapInputs_selected] at h
  exact DFunLike.congr_fun h x

theorem infinityOverlapLift_other (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    (infinityOverlapLift W b a v).comp (infinityFiniteInput W b (!b)) = v := by
  have h := congrArg (fun k : ChartPairRing W true true →ₐ[R] S ↦
    k.comp (infinityPairInput W (!b))) (infinityOverlapLift_restriction W b a v)
  exact h.trans (infinityOverlapInputs_other W b a v)

theorem infinityChartAddition_on_first_overlap [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W true →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
      (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) v).toRingHom) ≫
        infinityChartAddition W =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.productMap (a.comp (changeChart W true)) v).toRingHom) ≫
          oppositeMixedAddition W := by
  let k := infinityOverlapLift W false a v
  have hl : k.comp (infinityFiniteAffine W false) = a.comp (changeChart W true) :=
    congrArg (fun f : Overlap W true →ₐ[R] S ↦ f.comp (changeChart W true))
      (infinityOverlapLift_overlap W false a v)
  have hr := infinityOverlapLift_other W false a v
  have hp : k.comp (infinityFinitePair W false) =
      Algebra.TensorProduct.productMap (a.comp (changeChart W true)) v := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change k (infinityFiniteAffine W false x * infinityFiniteInput W false true y) = _
    rw [map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hl x) (DFunLike.congr_fun hr y)
  have h := infinityChartAddition_after_finite W false k
  rw [infinityOverlapLift_restriction] at h
  change _ = Spec.map (CommRingCat.ofHom k.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (infinityFinitePair W false).toRingHom) ≫
      oppositeMixedAddition W) at h
  rw [← Category.assoc, ← Spec.map_comp] at h
  change _ = Spec.map (CommRingCat.ofHom
    (k.comp (infinityFinitePair W false)).toRingHom) ≫ oppositeMixedAddition W at h
  rw [hp] at h
  exact h

theorem infinityChartAddition_on_second_overlap [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (v : Ring W true →ₐ[R] S) (a : Overlap W true →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap v
      (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)))).toRingHom) ≫
        infinityChartAddition W =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.productMap v (a.comp (changeChart W true))).toRingHom) ≫
          mixedChartAddition W := by
  let k := infinityOverlapLift W true a v
  have hr : k.comp (infinityFiniteAffine W true) = a.comp (changeChart W true) :=
    congrArg (fun f : Overlap W true →ₐ[R] S ↦ f.comp (changeChart W true))
      (infinityOverlapLift_overlap W true a v)
  have hl := infinityOverlapLift_other W true a v
  have hp : k.comp (infinityFinitePair W true) =
      Algebra.TensorProduct.productMap v (a.comp (changeChart W true)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change k (infinityFiniteInput W true false x * infinityFiniteAffine W true y) = _
    rw [map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hl x) (DFunLike.congr_fun hr y)
  have h := infinityChartAddition_after_finite W true k
  rw [infinityOverlapLift_restriction] at h
  change _ = Spec.map (CommRingCat.ofHom k.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (infinityFinitePair W true).toRingHom) ≫
      mixedChartAddition W) at h
  rw [← Category.assoc, ← Spec.map_comp] at h
  change _ = Spec.map (CommRingCat.ofHom
    (k.comp (infinityFinitePair W true)).toRingHom) ≫ mixedChartAddition W at h
  rw [hp] at h
  exact h

end WeierstrassCurve.CubicCharts
