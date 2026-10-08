/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityNegationChart
public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover
public import FLT.Mazur.WeierstrassProductBoundaryPoints
public import FLT.Mazur.WeierstrassAdditionSchemeCover

/-!
# An open cover for integral negation

The affine overlap and the output-Y negation neighborhood cover the Y chart.
Together with the affine chart they cover the whole glued cubic. All coverage
arguments work over arbitrary coefficient rings, including nonreduced rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Inclusion of the explicit negation neighborhood in the Y chart. -/
def infinityNegationInclusion :
    Spec (.of (InfinityNegationOpen W)) ⟶ chartScheme W 1 :=
  Spec.map (CommRingCat.ofHom (infinityNegationRestriction W).toRingHom)

instance infinityNegationInclusion_isOpenImmersion :
    IsOpenImmersion (infinityNegationInclusion W) :=
  IsOpenImmersion.of_isLocalization (infinityNegationDen W)

/-- The two concrete domains covering the Y chart. -/
def negationYCoverRing (b : Bool) : CommRingCat :=
  if b then .of (InfinityNegationOpen W) else .of (Overlap W 1 2)

/-- The original Y-chart coordinates restricted to either cover member. -/
def negationYCoverRestriction (b : Bool) : Coordinate W 1 →+* negationYCoverRing W b :=
  match b with
  | true => (infinityNegationRestriction W).toRingHom
  | false => (overlapRestriction W 1 2).toRingHom

/-- Every residue-field point belongs to one of the two negation domains. -/
theorem negationYCover_covers (p : PrimeSpectrum (Coordinate W 1)) :
    ∃ b, p ∈ Set.range (PrimeSpectrum.comap (negationYCoverRestriction W b)) := by
  let f : Coordinate W 1 →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (Coordinate W 1) p.asIdeal.ResidueField
  by_cases hz : f (coord W 1 2) = 0
  · have hf := chart_hom_eq_infinity_of_z_eq_zero W f hz
    have hd : f (infinityNegationDen W) = -1 := by
      rw [hf]
      simp [infinityNegationDen, chartNegationCoordinates,
        WeierstrassCurve.Projective.negY, AlgHom.commutes]
    have hu : IsUnit (f (infinityNegationDen W)) := hd.symm ▸ isUnit_neg_one
    let g : InfinityNegationOpen W →ₐ[R] p.asIdeal.ResidueField :=
      IsLocalization.Away.liftAlgHom (infinityNegationDen W) hu
    refine ⟨true, mem_range_comap_of_residue_lift p _ g.toRingHom ?_⟩
    intro a
    change g (infinityNegationRestriction W a) = f a
    exact IsLocalization.Away.lift_eq (infinityNegationDen W) hu a
  · refine ⟨false, mem_range_comap_of_residue_lift p _
      (overlapLift W 1 2 f (isUnit_iff_ne_zero.mpr hz)).toRingHom ?_⟩
    intro a
    exact DFunLike.congr_fun (overlapLift_restriction W 1 2 f
      (isUnit_iff_ne_zero.mpr hz)) a

/-- The affine overlap and the infinity negation neighborhood cover the Y chart. -/
def negationYCover : (chartScheme W 1).OpenCover where
  I₀ := Bool
  X b := Spec (negationYCoverRing W b)
  f b := Spec.map (CommRingCat.ofHom (negationYCoverRestriction W b))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨negationYCover_covers W, ?_⟩
    intro b
    cases b
    · exact overlapInclusion_isOpenImmersion W 1 2
    · exact infinityNegationInclusion_isOpenImmersion W

/-- The affine chart and the infinity neighborhood are the global negation domains. -/
def negationCoverScheme (b : Bool) : Scheme :=
  if b then Spec (.of (InfinityNegationOpen W)) else chartScheme W 2

/-- Each negation domain maps openly to the original glued cubic. -/
def negationCoverInclusion (b : Bool) : negationCoverScheme W b ⟶ integralCurve W :=
  match b with
  | false => integralCurveChart W 2
  | true => infinityNegationInclusion W ≫ integralCurveChart W 1

instance negationCoverInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (negationCoverInclusion W b) := by
  cases b
  · exact integralCurveChart_isOpenImmersion W 2
  · change IsOpenImmersion (infinityNegationInclusion W ≫ integralCurveChart W 1)
    infer_instance

/-- These two actual opens cover the whole integral cubic. -/
theorem negationCover_covers (x : integralCurve W) :
    ∃ b, ∃ y : negationCoverScheme W b, negationCoverInclusion W b y = x := by
  rcases integralCurve_yz_cover W x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · obtain ⟨b, t, ht⟩ := (negationYCover W).exists_eq y
    cases b
    · refine ⟨false, Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) t, ?_⟩
      change (Spec.map _ ≫ integralCurveChart W 2) t = integralCurveChart W 1 y
      rw [integralCurve_output_transition]
      change integralCurveChart W 1 ((negationYCover W).f false t) = _
      rw [ht]
    · exact ⟨true, t, congrArg (integralCurveChart W 1) ht⟩
  · exact ⟨false, z, rfl⟩

/-- An explicit two-member open cover on which integral negation is regular. -/
def negationCover : (integralCurve W).OpenCover where
  I₀ := Bool
  X := negationCoverScheme W
  f := negationCoverInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨negationCover_covers W, fun b => negationCoverInclusion_isOpenImmersion W b⟩

end FLT.Mazur.WeierstrassIntegralChart
