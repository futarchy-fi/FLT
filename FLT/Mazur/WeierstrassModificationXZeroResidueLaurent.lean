/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroResidueInfinity
public import FLT.Mazur.WeierstrassInfinityResidueGeometry
public import FLT.Mazur.WeierstrassSlopeLaurentGeometry

/-!
# The full start-zero slope transition in Laurent coordinates

The original start-zero infinity map has T=(v+a)/v on the entire slope
localization. This uses its actual cubic transition and original coefficients;
it does not introduce the positive-start incidence line or its node sections.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "P" => SlopeOpen a
local notation "z" => slopeZ a
local notation "A" => algebraMap K P a
local notation "f" => zeroResidueInfinityMap D hdepth k hk b3 b4 b6 h3 h4 h6
local notation "o" => zeroResidueBoundaryMap D hdepth k hk b3 b4 b6 h3 h4 h6
local notation "g" => zeroResidueOriginalMap D hdepth k hk b3 b4 b6 h3 h4 h6
local notation "u" => Units.mk0 a
  (IsUnit.ne_zero (IsUnit.map (residue R) (SplitNodeDepth.a₁_unit D)))

/-- Restriction of the actual start-zero overlap recovers every original affine function. -/
theorem zeroResidueBoundaryMap_base (w : WeierstrassIntegralChart.Coordinate W 2) :
    o (algebraMap _ (Overlap W 2 1) w) = g w :=
  IsLocalization.Away.lift_eq _
    (zeroResidueOriginalMap_y_isUnit D hdepth k hk b3 b4 b6 h3 h4 h6) w

/-- The original X/Y coordinate times the slope is one on the full start-zero chart. -/
theorem zeroResidueInfinityMap_x_mul : f (coord W 1 0) * z = 1 := by
  have h := congrArg o (overlapInverse_mul W 2 1)
  rw [map_mul, map_one, overlapCoord, zeroResidueBoundaryMap_base,
    zeroResidueOriginalMap_y] at h
  change o (transitionBase W 2 1 (coord W 1 0)) * z = 1
  rw [transitionBase_coord, map_mul, overlapCoord, zeroResidueBoundaryMap_base,
    zeroResidueOriginalMap_x, mul_assoc]
  exact h

/-- The whole start-zero infinity transition has X/Y equal to the inverse slope. -/
theorem zeroResidueInfinityMap_x : f (coord W 1 0) = ↑(slope_units a).1.unit⁻¹ := by
  apply (slope_units a).1.mul_right_cancel
  rw [zeroResidueInfinityMap_x_mul]
  exact (Units.inv_mul_eq_one.mpr (slope_units a).1.unit_spec).symm

/-- Extend the actual start-zero infinity transition over the original residue field. -/
def zeroResidueInfinityTensorMap : ChartScalarExtension K W 1 →ₐ[K] P :=
  AlgHom.liftEquiv R K _ _ f

/-- The tensor extension retains every original infinity function. -/
theorem zeroResidueInfinityTensorMap_tmul (r : K)
    (w : WeierstrassIntegralChart.Coordinate W 1) :
    zeroResidueInfinityTensorMap D hdepth k hk b3 b4 b6 h3 h4 h6 (r ⊗ₜ[R] w) =
      r • f w := rfl

/-- The tensor transition projects to the unchanged original infinity coordinate map. -/
@[reassoc] theorem zeroResidueInfinityTensorMap_projection :
    Spec.map (CommRingCat.ofHom
      (zeroResidueInfinityTensorMap D hdepth k hk b3 b4 b6 h3 h4 h6).toRingHom) ≫
        TensorOpenChart.projection = zeroResidueToInfinity D hdepth k hk b3 b4 b6 h3 h4 h6 := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun w => one_smul K (f w))

/-- The full start-zero Laurent map uses the actual original infinity equivalence. -/
def zeroResidueLaurentMap : K[T;T⁻¹] →ₐ[K] P :=
  (zeroResidueInfinityTensorMap D hdepth k hk b3 b4 b6 h3 h4 h6).comp
    (infinityResidueEquiv D hdepth).symm.toAlgHom

/-- The ordered Laurent generator is (v+a)/v on the entire original start-zero slope chart. -/
theorem zeroResidueLaurentMap_T :
    zeroResidueLaurentMap D hdepth k hk b3 b4 b6 h3 h4 h6 (LaurentPolynomial.T 1) =
      (z + A) * ↑(slope_units a).1.unit⁻¹ := by
  change zeroResidueInfinityTensorMap D hdepth k hk b3 b4 b6 h3 h4 h6
    ((infinityResidueEquiv D hdepth).symm (LaurentPolynomial.T 1)) = _
  rw [infinityResidueEquiv_symm_tangent, map_add, map_one, map_mul, AlgHom.commutes]
  rw [infinityTensorCoord, zeroResidueInfinityTensorMap_tmul, one_smul,
    zeroResidueInfinityMap_x]
  have hz : z * ↑(slope_units a).1.unit⁻¹ = 1 :=
    Units.mul_inv_eq_one.mpr (slope_units a).1.unit_spec
  rw [add_mul, hz]

/-- The original start-zero transition is the canonical slope map on every Laurent function. -/
theorem zeroResidueLaurentMap_eq :
    zeroResidueLaurentMap D hdepth k hk b3 b4 b6 h3 h4 h6 = slopeLaurentMap u := by
  apply slopeLaurent_hom_ext
  rw [zeroResidueLaurentMap_T]
  exact (slopeLaurentMap_T u).symm

/-- The Laurent description retains the complete original tensor transition. -/
theorem zeroResidueLaurentMap_spec :
    Spec.map (CommRingCat.ofHom
      (zeroResidueLaurentMap D hdepth k hk b3 b4 b6 h3 h4 h6).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (zeroResidueInfinityTensorMap D hdepth k hk b3 b4 b6 h3 h4 h6).toRingHom) ≫
          (infinityResidueIso D hdepth).inv := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
