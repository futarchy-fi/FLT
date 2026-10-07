/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProductBoundaryPoints
public import FLT.Mazur.WeierstrassProductOverlapScheme
public import FLT.Mazur.WeierstrassInfinityAdditionScheme
public import FLT.Mazur.WeierstrassAdditionSchemeCover

/-!
# A complete open cover of the Y-chart input product

Both inputs affine, a mixed infinity pair, and the pair of infinity points
are covered respectively by the affine input overlap, the polynomial output-Z
open, and the regular infinity domain. The cover is valid over every base ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Three domains distinguish the affine and boundary parts of the Y-chart product. -/
inductive YProductCoverIndex
  | affine | polynomial | infinity

/-- The actual rings of the three input domains. -/
def yProductCoverRing : YProductCoverIndex → CommRingCat
  | .affine => CommRingCat.of (ProductOverlap W 1 1 2 2)
  | .polynomial => CommRingCat.of (AdditionOutputOpen W 1 1 2)
  | .infinity => CommRingCat.of (InfinityAdditionOpen W)

/-- Restriction of the Y-chart input product to a cover member. -/
def yProductCoverRestriction (i : YProductCoverIndex) :
    ChartProduct W 1 1 →+* yProductCoverRing W i :=
  match i with
  | .affine => (productOverlapRestriction W 1 1 2 2).toRingHom
  | .polynomial => (additionOutputRestriction W 1 1 2).toRingHom
  | .infinity => (infinityAdditionRestriction W).toRingHom

/-- The three concrete domain inclusions as scheme morphisms. -/
def yProductCoverInclusion (i : YProductCoverIndex) :
    Spec (yProductCoverRing W i) ⟶ Spec (CommRingCat.of (ChartProduct W 1 1)) :=
  Spec.map (CommRingCat.ofHom (yProductCoverRestriction W i))

/-- Every member is genuinely open in the Y-chart input product. -/
instance yProductCoverInclusion_isOpenImmersion (i : YProductCoverIndex) :
    IsOpenImmersion (yProductCoverInclusion W i) := by
  cases i with
  | affine => exact productOverlapRestriction_isOpenImmersion W 1 1 2 2
  | polynomial => exact projectiveAdditionInclusion_isOpenImmersion W 1 1 2
  | infinity => exact infinityAdditionInclusion_isOpenImmersion W

/-- Residue-field cases prove that the three concrete opens cover every prime. -/
theorem yProductCoverInclusion_covers (p : PrimeSpectrum (ChartProduct W 1 1)) :
    ∃ i, p ∈ Set.range (PrimeSpectrum.comap (yProductCoverRestriction W i)) := by
  let f : ChartProduct W 1 1 →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (ChartProduct W 1 1) p.asIdeal.ResidueField
  have polynomial (h : f (chartProductAdditionCoordinates W 1 1 2) ≠ 0) :
      p ∈ Set.range (PrimeSpectrum.comap (yProductCoverRestriction W .polynomial)) := by
    let g : AdditionOutputOpen W 1 1 2 →ₐ[R] p.asIdeal.ResidueField :=
      IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W 1 1 2)
        (isUnit_iff_ne_zero.mpr h)
    refine mem_range_comap_of_residue_lift p _ g.toRingHom ?_
    intro a
    change g (additionOutputRestriction W 1 1 2 a) = f a
    exact IsLocalization.Away.lift_eq (chartProductAdditionCoordinates W 1 1 2)
      (isUnit_iff_ne_zero.mpr h) a
  by_cases hl : f (chartProductLeft W 1 1 (coord W 1 2)) = 0
  · by_cases hr : f (chartProductRight W 1 1 (coord W 1 2)) = 0
    · obtain ⟨g, hg⟩ := product_boundary_pair_lift W f hl hr
      refine ⟨.infinity, mem_range_comap_of_residue_lift p _ g.toRingHom ?_⟩
      exact fun a => DFunLike.congr_fun hg a
    · exact ⟨.polynomial, polynomial (product_add_left_boundary_z_ne_zero W 1 f hl hr)⟩
  · by_cases hr : f (chartProductRight W 1 1 (coord W 1 2)) = 0
    · exact ⟨.polynomial, polynomial (product_add_right_boundary_z_ne_zero W 1 f hl hr)⟩
    · refine ⟨.affine, mem_range_comap_of_residue_lift p _
        (productOverlapLift W 1 1 2 2 f
          (isUnit_iff_ne_zero.mpr hl) (isUnit_iff_ne_zero.mpr hr)).toRingHom ?_⟩
      exact fun a => DFunLike.congr_fun
        (productOverlapLift_restriction W 1 1 2 2 f
          (isUnit_iff_ne_zero.mpr hl) (isUnit_iff_ne_zero.mpr hr)) a

/-- All Y-chart input pairs are covered, including every boundary pair. -/
def yProductOpenCover : (Spec (CommRingCat.of (ChartProduct W 1 1))).OpenCover where
  I₀ := YProductCoverIndex
  X i := Spec (yProductCoverRing W i)
  f := yProductCoverInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨yProductCoverInclusion_covers W, inferInstance⟩

end FLT.Mazur.WeierstrassIntegralChart
