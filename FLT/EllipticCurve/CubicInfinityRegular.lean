/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicDenseComparison
public import FLT.EllipticCurve.CubicInfinityComparison

/-! # A schematically dense projective domain near the pair of infinities -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Every infinity-chart v-coordinate minus a coefficient is regular over any base. -/
theorem infinity_v_sub_mem_nonZeroDivisors (a : R) :
    coord W true 1 - algebraMap R (Ring W true) a ∈ nonZeroDivisors (Ring W true) := by
  let : Module.Free (Polynomial R) (AdjoinRoot (infinityPolynomial W)) :=
    (infinityPolynomial_monic W).free_adjoinRoot
  let e := infinityCoordinateRingEquiv W
  have he :
      e (coord W true 1 - algebraMap R (Ring W true) a) =
        algebraMap (Polynomial R) (AdjoinRoot (infinityPolynomial W))
          (Polynomial.X - Polynomial.C a) := by
    rw [map_sub, infinityCoordinateRingEquiv_coord_one, AlgEquiv.commutes, map_sub]
    rfl
  have hr := Module.Flat.isSMulRegular_of_isRegular
    (M := AdjoinRoot (infinityPolynomial W)) (Polynomial.monic_X_sub_C a).isRegular
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply e.injective
  have h := congrArg e hx
  rw [map_mul, he, map_zero, ← Algebra.smul_def] at h
  have hh : (Polynomial.X - Polynomial.C a) • e x =
      (Polynomial.X - Polynomial.C a) • (0 : AdjoinRoot (infinityPolynomial W)) := by
    simpa only [smul_zero] using h
  simpa only [map_zero] using hr hh

theorem infinityPair_v_difference_mem_nonZeroDivisors :
    infinityPairCoord W true 1 - infinityPairCoord W false 1 ∈
      nonZeroDivisors (ChartPairRing W true true) := by
  let A := Ring W true
  let E := W.map (algebraMap R A)
  let e := chartBaseChangeEquiv W A true
  have he : e (infinityPairCoord W true 1 - infinityPairCoord W false 1) =
      coord E true 1 - algebraMap A (Ring E true) (coord W true 1) := by
    rw [map_sub]
    exact congrArg₂ (· - ·) (chartBaseChangeEquiv_coord W A true 1)
      (e.commutes (coord W true 1))
  apply mem_nonZeroDivisors_of_injective e.injective
  rw [he]
  exact infinity_v_sub_mem_nonZeroDivisors E (coord W true 1)

private theorem regular_under_flat_algebra {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] {a : A} (ha : a ∈ nonZeroDivisors A) :
    algebraMap A B a ∈ nonZeroDivisors B := by
  have hi := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply hi
  simpa only [Algebra.smul_def, mul_zero] using hx

theorem infinitySlope_u_difference_mem_nonZeroDivisors :
    infinitySlopeCoord W true 0 - infinitySlopeCoord W false 0 ∈
      nonZeroDivisors (InfinitySlopeRing W) := by
  have hv := regular_under_flat_algebra (B := InfinitySlopeRing W)
    (infinityPair_v_difference_mem_nonZeroDivisors W)
  rw [map_sub] at hv
  change infinitySlopeCoord W true 1 - infinitySlopeCoord W false 1 ∈
    nonZeroDivisors (InfinitySlopeRing W) at hv
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply mem_nonZeroDivisors_iff_left.mp hv x
  rw [infinitySlope_relation, mul_assoc, hx, mul_zero]

/-- The projective output denominator restricted to the regular infinity-addition domain. -/
def infinityProjectiveDenominator : InfinityAdditionRing W :=
  infinityAdditionRestriction W
    (infinitySlopeRestriction W (projectiveAdditionDenominator W true true true))

/-- The projective formula is defined on a schematically dense open of the
infinity-addition domain, even over nonreduced bases. -/
theorem infinityProjectiveDenominator_mem_nonZeroDivisors :
    infinityProjectiveDenominator W ∈ nonZeroDivisors (InfinityAdditionRing W) := by
  have hu := regular_under_flat_algebra (B := InfinityAdditionRing W)
    (infinitySlope_u_difference_mem_nonZeroDivisors W)
  have hy : IsUnit (infinityAdditionRestriction W (infinitySumProjective W 1)) :=
    isUnit_iff_exists_inv.mpr ⟨infinityAdditionInv W,
      IsLocalization.Away.mul_invSelf (S := InfinityAdditionRing W)
        (infinitySumProjective W 1)⟩
  have h := congrArg (infinityAdditionRestriction W)
    (congrFun (infinitySlope_projective_comparison W) 1)
  simp only [Function.comp_apply, map_mul, map_pow] at h
  change infinityProjectiveDenominator W =
    infinityAdditionRestriction W
      (infinitySlopeCoord W true 0 - infinitySlopeCoord W false 0) ^ 3 *
        infinityAdditionRestriction W (infinitySumProjective W 1) at h
  rw [h]
  exact mul_mem (pow_mem hu 3) hy.mem_nonZeroDivisors

/-- A dense domain on which the infinity chord is also a normalized projective law. -/
abbrev InfinityProjectiveRing := Localization.Away (infinityProjectiveDenominator W)

/-- Restriction to the dense projective domain in the infinity-addition neighborhood. -/
def infinityProjectiveRestriction : InfinityAdditionRing W →ₐ[R] InfinityProjectiveRing W :=
  IsScalarTower.toAlgHom R (InfinityAdditionRing W) (InfinityProjectiveRing W)

theorem infinityProjectiveRestriction_injective :
    Function.Injective (infinityProjectiveRestriction W) :=
  IsLocalization.injective (InfinityProjectiveRing W)
    (Submonoid.powers_le.mpr (infinityProjectiveDenominator_mem_nonZeroDivisors W))

instance infinityProjectiveRestriction_schematic_dominance :
    IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (infinityProjectiveRestriction W).toRingHom)) :=
  specMap_schematic_dominance _ (infinityProjectiveRestriction_injective W)


/-- The dense domain factors through the normalized projective-addition chart. -/
def infinityProjectiveLift :
    ProjectiveAdditionRing W true true true →ₐ[R] InfinityProjectiveRing W :=
  IsLocalization.Away.liftAlgHom (projectiveAdditionDenominator W true true true)
    (f := (infinityProjectiveRestriction W).comp
      ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)))
    (isUnit_iff_exists_inv.mpr
      ⟨IsLocalization.Away.invSelf (infinityProjectiveDenominator W),
        IsLocalization.Away.mul_invSelf (S := InfinityProjectiveRing W)
          (infinityProjectiveDenominator W)⟩)

theorem infinityProjectiveLift_restriction :
    (infinityProjectiveLift W).comp (projectiveAdditionRestriction W true true true) =
      (infinityProjectiveRestriction W).comp
        ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)) := by
  apply AlgHom.ext
  intro x
  simp [infinityProjectiveLift, projectiveAdditionRestriction]

/-- The infinity law agrees with the projective law on this schematically dense domain. -/
theorem infinityProjectiveLift_addition :
    Spec.map (CommRingCat.ofHom (infinityProjectiveRestriction W).toRingHom) ≫
        infinityAddition W =
      Spec.map (CommRingCat.ofHom (infinityProjectiveLift W).toRingHom) ≫
        projectiveAddition W true true true := by
  unfold infinityAddition projectiveAddition
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  exact infinity_projective_addition_agreement W true
    (infinityProjectiveRestriction W) (infinityProjectiveLift W)
    (infinityProjectiveLift_restriction W).symm

/-- The same dense comparison remains valid after any flat base change,
in particular after restriction to an open intersection used in descent. -/
theorem infinityProjective_flat_schematic_dominance
    {S : Type u} [CommRing S] [Algebra (InfinityAdditionRing W) S]
    [Module.Flat (InfinityAdditionRing W) S] :
    IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (algebraMap S
        (Localization.Away (algebraMap (InfinityAdditionRing W) S
          (infinityProjectiveDenominator W)))))) := by
  apply specMap_schematic_dominance
  exact IsLocalization.injective _
    (Submonoid.powers_le.mpr (regular_under_flat_algebra (B := S)
      (infinityProjectiveDenominator_mem_nonZeroDivisors W)))

end WeierstrassCurve.CubicCharts
