/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInverseNeighborhood
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# The inverse neighborhood and affine overlap cover the Y chart

The constructed inverse neighborhood contains the entire zero section. Every
residue-field point outside the affine overlap is that section, proving the
two-member open cover used to descend the inverse law to the whole curve.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The actual negation pair specializes to the infinity pair at zero. -/
theorem infinityNegationInput_zero :
    (infinityNegationZero W).comp (infinityNegationInput W) = infinityPairEvaluation W := by
  apply chartProduct_hom_ext W 1 1
  · rw [AlgHom.comp_assoc, infinityNegationInput_left, infinityNegationZero_restriction,
      infinityPairEvaluation, chartProductEvaluation_left]
  · rw [AlgHom.comp_assoc, infinityNegationInput_right, infinityNegationZero_chart,
      infinityPairEvaluation, chartProductEvaluation_right]

/-- The extra inverse-formula factor equals one along the entire zero section. -/
theorem infinityNegationFactor_zero :
    infinityNegationZero W (infinityNegationFactor W) = 1 := by
  simp [infinityNegationFactor, infinityNegationZero_inverse]

/-- Both factors of the slope-neighborhood denominator equal one at zero. -/
theorem infinityInverseDen_zero :
    infinityNegationZero W (infinityInverseDen W) = 1 := by
  rw [infinityInverseDen, map_mul, infinityNegationFactor_zero, one_mul]
  change ((infinityNegationZero W).comp (infinityNegationInput W))
    (infinityDen W (AlgHom.id R _)) = 1
  rw [infinityNegationInput_zero, infinityDen_map, AlgHom.comp_id,
    infinityPairEvaluation_den]

/-- Lift the zero section through the first inverse-neighborhood localization. -/
def infinityInverseZeroSlope : InfinityInverseSlopeOpen W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityInverseDen W)
    (show IsUnit (infinityNegationZero W (infinityInverseDen W)) by
      rw [infinityInverseDen_zero]
      exact isUnit_one)

/-- This lift retains the original zero section of the negation neighborhood. -/
theorem infinityInverseZeroSlope_restriction :
    (infinityInverseZeroSlope W).comp (infinityInverseSlopeRestriction W) =
      infinityNegationZero W := by
  apply AlgHom.ext
  intro a
  change infinityInverseZeroSlope W (algebraMap _ _ a) = _
  simp only [infinityInverseZeroSlope, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- On the original slope domain it is the already constructed infinity-pair lift. -/
theorem infinityInverseZeroSlope_map :
    (infinityInverseZeroSlope W).comp (infinityInverseSlopeMap W) =
      infinityPairSlopeLift W := by
  apply IsLocalization.algHom_ext (Submonoid.powers (infinityDen W (AlgHom.id R _)))
  change ((infinityInverseZeroSlope W).comp (infinityInverseSlopeMap W)).comp
    (infinitySlopeRestriction W) = (infinityPairSlopeLift W).comp (infinitySlopeRestriction W)
  rw [AlgHom.comp_assoc, infinityInverseSlopeMap_inputs, ← AlgHom.comp_assoc,
    infinityInverseZeroSlope_restriction, infinityNegationInput_zero, infinityPairSlopeLift_comp]

/-- The normalizing output coordinate is also one along zero. -/
theorem infinityInverseOutputY_zero :
    infinityInverseZeroSlope W (infinityInverseOutputY W) = 1 := by
  have h := DFunLike.congr_fun (infinityInverseZeroSlope_map W)
    (infinityOutputCoordinates W 1)
  exact h.trans (infinityPairSlopeLift_output W 1)

/-- The zero section lifts through the full inverse neighborhood. -/
def infinityInverseZero : InfinityInverseOpen W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityInverseOutputY W)
    (show IsUnit (infinityInverseZeroSlope W (infinityInverseOutputY W)) by
      rw [infinityInverseOutputY_zero]
      exact isUnit_one)

/-- The second zero lift restricts to the first one. -/
theorem infinityInverseZero_output :
    (infinityInverseZero W).comp (infinityInverseOutputRestriction W) =
      infinityInverseZeroSlope W := by
  apply AlgHom.ext
  intro a
  change infinityInverseZero W (algebraMap _ _ a) = _
  simp only [infinityInverseZero, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The entire zero section belongs to the inverse neighborhood. -/
theorem infinityInverseZero_restriction :
    (infinityInverseZero W).comp (infinityInverseRestriction W) =
      chartInfinityEvaluation W := by
  rw [infinityInverseRestriction, infinityInverseNegationRestriction,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, infinityInverseZero_output,
    infinityInverseZeroSlope_restriction, infinityNegationZero_restriction]

/-- The two chart domains used to prove an inverse law on all of Y. -/
def infinityInverseCoverRing (c : Bool) : CommRingCat :=
  if c then .of (InfinityInverseOpen W) else .of (Overlap W 1 2)

/-- Restriction to either the affine overlap or the inverse neighborhood. -/
def infinityInverseCoverRestriction (c : Bool) :
    Coordinate W 1 →+* infinityInverseCoverRing W c :=
  match c with
  | true => (infinityInverseRestriction W).toRingHom
  | false => (overlapRestriction W 1 2).toRingHom

/-- The two domains cover every prime of the Y-chart coordinate ring. -/
theorem infinityInverseCover_covers (p : PrimeSpectrum (Coordinate W 1)) :
    ∃ c, p ∈ Set.range (PrimeSpectrum.comap (infinityInverseCoverRestriction W c)) := by
  let f : Coordinate W 1 →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (Coordinate W 1) p.asIdeal.ResidueField
  by_cases hz : f (coord W 1 2) = 0
  · have hf := chart_hom_eq_infinity_of_z_eq_zero W f hz
    let g := (Algebra.ofId R p.asIdeal.ResidueField).comp (infinityInverseZero W)
    refine ⟨true, mem_range_comap_of_residue_lift p _ g.toRingHom ?_⟩
    intro a
    change g (infinityInverseRestriction W a) = f a
    have he : g.comp (infinityInverseRestriction W) = f := by
      rw [hf]
      dsimp only [g]
      rw [AlgHom.comp_assoc, infinityInverseZero_restriction]
      apply AlgHom.coe_ringHom_injective
      exact (chartInfinityEvaluation_base W).symm
    exact DFunLike.congr_fun he a
  · refine ⟨false, mem_range_comap_of_residue_lift p _
      (overlapLift W 1 2 f (isUnit_iff_ne_zero.mpr hz)).toRingHom ?_⟩
    intro a
    exact DFunLike.congr_fun (overlapLift_restriction W 1 2 f
      (isUnit_iff_ne_zero.mpr hz)) a

/-- An explicit open cover of the whole Y chart for the inverse law. -/
def infinityInverseCover : (Spec (.of (Coordinate W 1))).OpenCover where
  I₀ := Bool
  X c := Spec (infinityInverseCoverRing W c)
  f c := Spec.map (CommRingCat.ofHom (infinityInverseCoverRestriction W c))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨infinityInverseCover_covers W, ?_⟩
    intro c
    cases c
    · exact overlapInclusion_isOpenImmersion W 1 2
    · exact infinityInverseInclusion_isOpenImmersion W

end FLT.Mazur.WeierstrassIntegralChart
