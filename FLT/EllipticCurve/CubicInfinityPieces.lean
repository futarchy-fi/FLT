/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityCover
public import FLT.EllipticCurve.CubicMixedOpposite

/-! # Addition morphisms on every piece of the infinity-chart cover -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Either input on the open where the selected input is finite. -/
def infinityFiniteInput (b c : Bool) : Ring W true →ₐ[R] InfinityFiniteRing W b :=
  (infinityFiniteRestriction W b).comp (infinityPairInput W c)

/-- The selected finite input factors through the intersection of the two charts. -/
def infinityFiniteOverlap (b : Bool) : Overlap W true →ₐ[R] InfinityFiniteRing W b :=
  IsLocalization.Away.liftAlgHom (coord W true 1) (f := infinityFiniteInput W b b)
    (isUnit_iff_exists_inv.mpr ⟨IsLocalization.Away.invSelf (infinityPairCoord W b 1),
      IsLocalization.Away.mul_invSelf (S := InfinityFiniteRing W b) (infinityPairCoord W b 1)⟩)

theorem infinityFiniteOverlap_restriction (b : Bool) (x : Ring W true) :
    infinityFiniteOverlap W b (algebraMap (Ring W true) (Overlap W true) x) =
      infinityFiniteInput W b b x := by
  simp [infinityFiniteOverlap, IsLocalization.Away.liftAlgHom_apply]

/-- The selected input expressed in the ordinary affine chart. -/
def infinityFiniteAffine (b : Bool) : Ring W false →ₐ[R] InfinityFiniteRing W b :=
  (infinityFiniteOverlap W b).comp (changeChart W true)

/-- Changing coordinates preserves the actual input point in the glued cubic. -/
theorem infinityFiniteAffine_same_point (b : Bool) :
    Spec.map (CommRingCat.ofHom (infinityFiniteAffine W b).toRingHom) ≫ affineChart W =
      Spec.map (CommRingCat.ofHom (infinityFiniteInput W b b).toRingHom) ≫ infinityChart W := by
  change Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom ≫
    CommRingCat.ofHom (infinityFiniteOverlap W b).toRingHom) ≫ affineChart W = _
  rw [Spec.map_comp, Category.assoc, changeChart_true_to_scheme]
  unfold overlapInclusion
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (infinityFiniteOverlap_restriction W b)

/-- Both inputs after changing the selected finite input to the ordinary chart. -/
def infinityFinitePair : ∀ b, ChartPairRing W b (!b) →ₐ[R] InfinityFiniteRing W b
  | false => Algebra.TensorProduct.productMap
      (infinityFiniteAffine W false) (infinityFiniteInput W false true)
  | true => Algebra.TensorProduct.productMap
      (infinityFiniteInput W true false) (infinityFiniteAffine W true)

/-- Pull back the appropriate descended mixed addition to a finite-input open. -/
def infinityFiniteAddition [W.IsElliptic] :
    ∀ b, Spec (.of (InfinityFiniteRing W b)) ⟶ scheme W
  | false => Spec.map (CommRingCat.ofHom (infinityFinitePair W false).toRingHom) ≫
      oppositeMixedAddition W
  | true => Spec.map (CommRingCat.ofHom (infinityFinitePair W true).toRingHom) ≫
      mixedChartAddition W

@[reassoc (attr := simp)] theorem infinityFiniteAddition_toBase [W.IsElliptic] (b : Bool) :
    infinityFiniteAddition W b ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityFiniteRing W b))) := by
  cases b
  · change (Spec.map (CommRingCat.ofHom (infinityFinitePair W false).toRingHom) ≫
      oppositeMixedAddition W) ≫ toBase W = _
    rw [Category.assoc, oppositeMixedAddition_toBase, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (infinityFinitePair W false).comp_algebraMap
  · change (Spec.map (CommRingCat.ofHom (infinityFinitePair W true).toRingHom) ≫
      mixedChartAddition W) ≫ toBase W = _
    rw [Category.assoc, mixedChartAddition_toBase, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (infinityFinitePair W true).comp_algebraMap

/-- Actual addition morphisms on all three domains of the infinity-chart cover.
Their complete pairwise gluing remains a separate obligation. -/
def infinityCoverAddition [W.IsElliptic] :
    ∀ i, Spec (.of (InfinityCoverRing W i)) ⟶ scheme W
  | none => infinityAddition W
  | some b => infinityFiniteAddition W b

@[reassoc (attr := simp)] theorem infinityCoverAddition_toBase [W.IsElliptic] (i : Option Bool) :
    infinityCoverAddition W i ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityCoverRing W i))) := by
  cases i with
  | none => exact infinityAddition_toBase W
  | some b => exact infinityFiniteAddition_toBase W b

end WeierstrassCurve.CubicCharts
