/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicMixedOpposite
public import FLT.EllipticCurve.CubicAffineCommutativity

/-! # Restriction of mixed addition to ordinary affine inputs -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem mixedChartAddition_after_finite [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S] (f : MixedAffineRing W →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (f.comp (mixedAffineRestriction W)).toRingHom) ≫
        mixedChartAddition W =
      Spec.map (CommRingCat.ofHom (f.comp (mixedAffineInputs W)).toRingHom) ≫
        affineAddition W := by
  have h : Spec.map (CommRingCat.ofHom (mixedAffineRestriction W).toRingHom) ≫
      mixedChartAddition W = mixedAffineAddition W := mixedChartAddition_restrict W 0
  change Spec.map (CommRingCat.ofHom (mixedAffineRestriction W).toRingHom ≫
    CommRingCat.ofHom f.toRingHom) ≫ mixedChartAddition W = _
  rw [Spec.map_comp, Category.assoc, h]
  unfold mixedAffineAddition
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The mixed finite-input localization evaluated from a chart-overlap point. -/
def mixedOverlapLift {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (b : Ring W false →ₐ[R] S) :
    MixedAffineRing W →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (mixedFirstZ W)
    (f := Algebra.TensorProduct.productMap
      (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) b)
    (isUnit_iff_exists_inv.mpr ⟨a (inv W true), by
      change _ * a (inv W true) = 1
      simp only [mixedFirstZ, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.productMap_left_apply]
      change a (loc W true 1) * a (inv W true) = 1
      rw [← map_mul, loc_mul_inv, map_one]⟩)

theorem mixedOverlapLift_restriction {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (b : Ring W false →ₐ[R] S) :
    (mixedOverlapLift W a b).comp (mixedAffineRestriction W) =
      Algebra.TensorProduct.productMap
        (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) b := by
  apply AlgHom.ext
  intro x
  simp [mixedOverlapLift, mixedAffineRestriction]

theorem mixedOverlapLift_overlap {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (b : Ring W false →ₐ[R] S) :
    (mixedOverlapLift W a b).comp (mixedAffineOverlap W) = a := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coord W true 1))
  apply AlgHom.ext
  intro x
  change mixedOverlapLift W a b
    (mixedAffineOverlap W (algebraMap (Ring W true) (Overlap W true) x)) = _
  have hl : mixedAffineOverlap W (algebraMap (Ring W true) (Overlap W true) x) =
      mixedAffineLeft W x := by
    simp [mixedAffineOverlap, IsLocalization.Away.liftAlgHom_apply]
  rw [hl]
  have h := congrArg (fun k : ChartPairRing W true false →ₐ[R] S ↦
    k.comp (Algebra.TensorProduct.includeLeft :
      Ring W true →ₐ[R] ChartPairRing W true false)) (mixedOverlapLift_restriction W a b)
  rw [Algebra.TensorProduct.productMap_left] at h
  exact DFunLike.congr_fun h x

theorem mixedOverlapLift_inputs {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (b : Ring W false →ₐ[R] S) :
    (mixedOverlapLift W a b).comp (mixedAffineInputs W) =
      Algebra.TensorProduct.productMap (a.comp (changeChart W true)) b := by
  have hleft : (mixedOverlapLift W a b).comp (mixedAffineFirst W) =
      a.comp (changeChart W true) := by
    change ((mixedOverlapLift W a b).comp (mixedAffineOverlap W)).comp
      (changeChart W true) = _
    rw [mixedOverlapLift_overlap]
  have hright : (mixedOverlapLift W a b).comp (mixedAffineRight W) = b := by
    apply AlgHom.ext
    intro x
    have h := congrArg (fun k : ChartPairRing W true false →ₐ[R] S ↦
      k.comp (Algebra.TensorProduct.includeRight :
        Ring W false →ₐ[R] ChartPairRing W true false)) (mixedOverlapLift_restriction W a b)
    rw [Algebra.TensorProduct.productMap_right] at h
    exact DFunLike.congr_fun h x
  apply Algebra.TensorProduct.ext'
  intro x y
  change mixedOverlapLift W a b (mixedAffineFirst W x * mixedAffineRight W y) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hleft x) (DFunLike.congr_fun hright y)

/-- On the overlap of the input charts, mixed and affine addition agree as morphisms. -/
theorem mixedChartAddition_on_overlap [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (b : Ring W false →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
      (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) b).toRingHom) ≫
        mixedChartAddition W =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.productMap (a.comp (changeChart W true)) b).toRingHom) ≫
          affineAddition W := by
  have h := mixedChartAddition_after_finite W (mixedOverlapLift W a b)
  rw [mixedOverlapLift_restriction, mixedOverlapLift_inputs] at h
  exact h


theorem affineAddition_comm_eval [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (a b : Ring W false →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
        affineAddition W =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap b a).toRingHom) ≫
        affineAddition W := by
  have hs : (Algebra.TensorProduct.productMap b a).comp (affinePairSwap W).toAlgHom =
      Algebra.TensorProduct.productMap a b := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact mul_comm _ _
  have h := congrArg (fun k ↦
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap b a).toRingHom) ≫ k)
    (affineAddition_comm W)
  rw [← Category.assoc, ← Spec.map_comp] at h
  have he : CommRingCat.ofHom (affinePairSwap W).toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.productMap b a).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom := by
    exact congrArg (fun f : AffinePairRing W →ₐ[R] S ↦ CommRingCat.ofHom f.toRingHom) hs
  rw [he] at h
  exact h

/-- The opposite mixed chart also restricts to the existing affine addition. -/
theorem oppositeMixedAddition_on_overlap [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Ring W false →ₐ[R] S) (b : Overlap W true →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a
      (b.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)))).toRingHom) ≫
        oppositeMixedAddition W =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.productMap a (b.comp (changeChart W true))).toRingHom) ≫
          affineAddition W := by
  let c := b.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))
  have hs : (Algebra.TensorProduct.productMap a c).comp (mixedPairSwap W).toAlgHom =
      Algebra.TensorProduct.productMap c a := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact mul_comm _ _
  unfold oppositeMixedAddition
  rw [← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (mixedPairSwap W).toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.productMap a c).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.productMap c a).toRingHom := by
    exact congrArg (fun f : ChartPairRing W true false →ₐ[R] S ↦
      CommRingCat.ofHom f.toRingHom) hs
  change Spec.map (CommRingCat.ofHom (mixedPairSwap W).toRingHom ≫
    CommRingCat.ofHom (Algebra.TensorProduct.productMap a c).toRingHom) ≫
      mixedChartAddition W = _
  rw [he]
  exact (mixedChartAddition_on_overlap W b a).trans
    (affineAddition_comm_eval W (b.comp (changeChart W true)) a)

end WeierstrassCurve.CubicCharts
