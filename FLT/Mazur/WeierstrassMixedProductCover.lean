/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassYProductCover

/-!
# Complete covers of the mixed input-chart products

If at least one input is already on the Z-chart, the affine input overlap and
the polynomial output-Z open cover the product. This includes both mixed
Y/Z products and the all-affine product, over arbitrary base rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k : Fin 3)

/-- The affine overlap and polynomial output domain for a product with an affine input. -/
def mixedProductCoverRing : Bool → CommRingCat
  | true => CommRingCat.of (ProductOverlap W j k 2 2)
  | false => CommRingCat.of (AdditionOutputOpen W j k 2)

/-- Restrict the input product to one of the two concrete domains. -/
def mixedProductCoverRestriction (b : Bool) :
    ChartProduct W j k →+* mixedProductCoverRing W j k b :=
  match b with
  | true => (productOverlapRestriction W j k 2 2).toRingHom
  | false => (additionOutputRestriction W j k 2).toRingHom

/-- The concrete scheme inclusions of the two domains. -/
def mixedProductCoverInclusion (b : Bool) :
    Spec (mixedProductCoverRing W j k b) ⟶ Spec (CommRingCat.of (ChartProduct W j k)) :=
  Spec.map (CommRingCat.ofHom (mixedProductCoverRestriction W j k b))

/-- Both domains are open subschemes of the input product. -/
instance mixedProductCoverInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (mixedProductCoverInclusion W j k b) := by
  cases b with
  | false => exact projectiveAdditionInclusion_isOpenImmersion W j k 2
  | true => exact productOverlapRestriction_isOpenImmersion W j k 2 2

/-- With at least one affine input, the two domains cover every residue-field point. -/
theorem mixedProductCoverInclusion_covers (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2)
    (ha : j = 2 ∨ k = 2) (p : PrimeSpectrum (ChartProduct W j k)) :
    ∃ b, p ∈ Set.range (PrimeSpectrum.comap (mixedProductCoverRestriction W j k b)) := by
  let f : ChartProduct W j k →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (ChartProduct W j k) p.asIdeal.ResidueField
  have affine (hl : f (chartProductLeft W j k (coord W j 2)) ≠ 0)
      (hr : f (chartProductRight W j k (coord W k 2)) ≠ 0) :
      p ∈ Set.range (PrimeSpectrum.comap (mixedProductCoverRestriction W j k true)) := by
    refine mem_range_comap_of_residue_lift p _
      (productOverlapLift W j k 2 2 f
        (isUnit_iff_ne_zero.mpr hl) (isUnit_iff_ne_zero.mpr hr)).toRingHom ?_
    exact fun a => DFunLike.congr_fun
      (productOverlapLift_restriction W j k 2 2 f
        (isUnit_iff_ne_zero.mpr hl) (isUnit_iff_ne_zero.mpr hr)) a
  have polynomial (h : f (chartProductAdditionCoordinates W j k 2) ≠ 0) :
      p ∈ Set.range (PrimeSpectrum.comap (mixedProductCoverRestriction W j k false)) := by
    let g : AdditionOutputOpen W j k 2 →ₐ[R] p.asIdeal.ResidueField :=
      IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W j k 2)
        (isUnit_iff_ne_zero.mpr h)
    refine mem_range_comap_of_residue_lift p _ g.toRingHom ?_
    intro a
    change g (additionOutputRestriction W j k 2 a) = f a
    exact IsLocalization.Away.lift_eq (chartProductAdditionCoordinates W j k 2)
      (isUnit_iff_ne_zero.mpr h) a
  rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
  · rcases ha with ha | ha <;> norm_num at ha
  · have hr : f (chartProductRight W 1 2 (coord W 2 2)) ≠ 0 := by
      rw [coord_self, map_one, map_one]
      exact one_ne_zero
    by_cases hl : f (chartProductLeft W 1 2 (coord W 1 2)) = 0
    · exact ⟨false, polynomial (product_add_left_boundary_z_ne_zero W 2 f hl hr)⟩
    · exact ⟨true, affine hl hr⟩
  · have hl : f (chartProductLeft W 2 1 (coord W 2 2)) ≠ 0 := by
      rw [coord_self, map_one, map_one]
      exact one_ne_zero
    by_cases hr : f (chartProductRight W 2 1 (coord W 1 2)) = 0
    · exact ⟨false, polynomial (product_add_right_boundary_z_ne_zero W 2 f hl hr)⟩
    · exact ⟨true, affine hl hr⟩
  · apply Exists.intro true
    apply affine <;> rw [coord_self, map_one, map_one] <;> exact one_ne_zero

/-- A complete two-member open cover when one input is affine. -/
def mixedProductOpenCover (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2)
    (ha : j = 2 ∨ k = 2) : (Spec (CommRingCat.of (ChartProduct W j k))).OpenCover where
  I₀ := Bool
  X b := Spec (mixedProductCoverRing W j k b)
  f := mixedProductCoverInclusion W j k
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨mixedProductCoverInclusion_covers W j k hj hk ha, inferInstance⟩

end FLT.Mazur.WeierstrassIntegralChart
