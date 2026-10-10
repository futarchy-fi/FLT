/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityIdentityNeighborhood
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# An identity neighborhood and the affine overlap cover the Y chart

The new identity neighborhoods contain the entire zero section. Every
residue-field point outside the affine overlap is that section, proving the
two-member open cover used to descend the identity laws to the whole curve.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Both identity inputs specialize to the original infinity pair at zero. -/
theorem infinityIdentityInput_zero (b : Bool) :
    (chartInfinityEvaluation (S := R) W).comp (infinityIdentityInput W b) =
      infinityPairEvaluation W := by
  cases b <;> apply chartProduct_hom_ext W 1 1 <;>
    simp only [infinityIdentityInput, Bool.false_eq_true, ↓reduceIte, AlgHom.comp_assoc,
      infinityPairEvaluation, chartProductAtRightInfinity_left,
      chartProductAtRightInfinity_right, chartProductAtLeftInfinity_left,
      chartProductAtLeftInfinity_right, chartProductEvaluation_left,
      chartProductEvaluation_right, AlgHom.comp_id]
  all_goals
    apply hom_ext
    intro i
    fin_cases i <;> simp

/-- The pulled-back slope denominator is one at zero. -/
theorem infinityIdentityDen_zero (b : Bool) :
    chartInfinityEvaluation (S := R) W (infinityIdentityDen W b) = 1 := by
  change ((chartInfinityEvaluation (S := R) W).comp (infinityIdentityInput W b))
    (infinityDen W (AlgHom.id R _)) = 1
  rw [infinityIdentityInput_zero, infinityDen_map, AlgHom.comp_id, infinityPairEvaluation_den]

/-- Lift the zero section through the first identity-neighborhood localization. -/
def infinityIdentityZeroSlope (b : Bool) : InfinityIdentitySlopeOpen W b →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityIdentityDen W b)
    (show IsUnit (chartInfinityEvaluation (S := R) W (infinityIdentityDen W b)) by
      rw [infinityIdentityDen_zero]
      exact isUnit_one)

/-- This lift retains the original infinity evaluation on the Y chart. -/
theorem infinityIdentityZeroSlope_restriction (b : Bool) :
    (infinityIdentityZeroSlope W b).comp (infinityIdentitySlopeRestriction W b) =
      chartInfinityEvaluation W := by
  apply AlgHom.ext
  intro a
  change infinityIdentityZeroSlope W b (algebraMap _ _ a) = _
  simp only [infinityIdentityZeroSlope, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- On the original slope domain it is the already constructed infinity-pair lift. -/
theorem infinityIdentityZeroSlope_map (b : Bool) :
    (infinityIdentityZeroSlope W b).comp (infinityIdentitySlopeMap W b) =
      infinityPairSlopeLift W := by
  apply IsLocalization.algHom_ext (Submonoid.powers (infinityDen W (AlgHom.id R _)))
  change ((infinityIdentityZeroSlope W b).comp (infinityIdentitySlopeMap W b)).comp
    (infinitySlopeRestriction W) = (infinityPairSlopeLift W).comp (infinitySlopeRestriction W)
  rw [AlgHom.comp_assoc, infinityIdentitySlopeMap_inputs, ← AlgHom.comp_assoc,
    infinityIdentityZeroSlope_restriction, infinityIdentityInput_zero, infinityPairSlopeLift_comp]

/-- The normalizing output coordinate is also one along zero. -/
theorem infinityIdentityOutputY_zero (b : Bool) :
    infinityIdentityZeroSlope W b (infinityIdentityOutputY W b) = 1 := by
  have h := DFunLike.congr_fun (infinityIdentityZeroSlope_map W b)
    (infinityOutputCoordinates W 1)
  exact h.trans (infinityPairSlopeLift_output W 1)

/-- The zero section lifts through the full identity neighborhood. -/
def infinityIdentityZero (b : Bool) : InfinityIdentityOpen W b →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityIdentityOutputY W b)
    (show IsUnit (infinityIdentityZeroSlope W b (infinityIdentityOutputY W b)) by
      rw [infinityIdentityOutputY_zero]
      exact isUnit_one)

/-- The second zero lift restricts to the first one. -/
theorem infinityIdentityZero_output (b : Bool) :
    (infinityIdentityZero W b).comp (infinityIdentityOutputRestriction W b) =
      infinityIdentityZeroSlope W b := by
  apply AlgHom.ext
  intro a
  change infinityIdentityZero W b (algebraMap _ _ a) = _
  simp only [infinityIdentityZero, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The entire zero section belongs to the identity neighborhood. -/
theorem infinityIdentityZero_restriction (b : Bool) :
    (infinityIdentityZero W b).comp (infinityIdentityRestriction W b) =
      chartInfinityEvaluation W := by
  rw [infinityIdentityRestriction, ← AlgHom.comp_assoc, infinityIdentityZero_output,
    infinityIdentityZeroSlope_restriction]

/-- The two chart domains used to prove an identity law on all of Y. -/
def infinityIdentityCoverRing (b c : Bool) : CommRingCat :=
  if c then .of (InfinityIdentityOpen W b) else .of (Overlap W 1 2)

/-- Restriction to either the affine overlap or the identity neighborhood. -/
def infinityIdentityCoverRestriction (b c : Bool) :
    Coordinate W 1 →+* infinityIdentityCoverRing W b c :=
  match c with
  | true => (infinityIdentityRestriction W b).toRingHom
  | false => (overlapRestriction W 1 2).toRingHom

/-- The two domains cover every prime of the Y-chart coordinate ring. -/
theorem infinityIdentityCover_covers (b : Bool) (p : PrimeSpectrum (Coordinate W 1)) :
    ∃ c, p ∈ Set.range (PrimeSpectrum.comap (infinityIdentityCoverRestriction W b c)) := by
  let f : Coordinate W 1 →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (Coordinate W 1) p.asIdeal.ResidueField
  by_cases hz : f (coord W 1 2) = 0
  · have hf := chart_hom_eq_infinity_of_z_eq_zero W f hz
    let g := (Algebra.ofId R p.asIdeal.ResidueField).comp (infinityIdentityZero W b)
    refine ⟨true, mem_range_comap_of_residue_lift p _ g.toRingHom ?_⟩
    intro a
    change g (infinityIdentityRestriction W b a) = f a
    have he : g.comp (infinityIdentityRestriction W b) = f := by
      rw [hf]
      dsimp only [g]
      rw [AlgHom.comp_assoc, infinityIdentityZero_restriction]
      apply AlgHom.coe_ringHom_injective
      exact (chartInfinityEvaluation_base W).symm
    exact DFunLike.congr_fun he a
  · refine ⟨false, mem_range_comap_of_residue_lift p _
      (overlapLift W 1 2 f (isUnit_iff_ne_zero.mpr hz)).toRingHom ?_⟩
    intro a
    exact DFunLike.congr_fun (overlapLift_restriction W 1 2 f
      (isUnit_iff_ne_zero.mpr hz)) a

/-- An explicit open cover of the whole Y chart for either identity law. -/
def infinityIdentityCover (b : Bool) : (Spec (.of (Coordinate W 1))).OpenCover where
  I₀ := Bool
  X c := Spec (infinityIdentityCoverRing W b c)
  f c := Spec.map (CommRingCat.ofHom (infinityIdentityCoverRestriction W b c))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨infinityIdentityCover_covers W b, ?_⟩
    intro c
    cases c
    · exact overlapInclusion_isOpenImmersion W 1 2
    · exact infinityIdentityInclusion_isOpenImmersion W b

end FLT.Mazur.WeierstrassIntegralChart
