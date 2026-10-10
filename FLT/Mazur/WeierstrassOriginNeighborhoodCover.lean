/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIdeal
public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover

/-!
# The parameter neighborhood and affine chart cover the original cubic

The principal neighborhood constructed from the original infinity equation
contains the actual zero section. Together with the original affine chart it
covers the whole cubic over every coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A prime where z vanishes cannot contain the origin denominator. -/
theorem originDenominator_notMem_of_z_mem (p : PrimeSpectrum (Coordinate W 1))
    (hz : coord W 1 2 ∈ p.asIdeal) : originDenominator W ∉ p.asIdeal := by
  have hx : coord W 1 0 ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 3 (by
    rw [← originDenominator_relation]
    exact p.asIdeal.mul_mem_right _ hz)
  have he : Ideal.Quotient.mk p.asIdeal (originDenominator W) = 1 := by
    simp [originDenominator, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
      Ideal.Quotient.eq_zero_iff_mem.mpr hz]
  intro hd
  exact one_ne_zero (he.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hd))

/-- The actual parameter neighborhood as an open subscheme of the original cubic. -/
def originNeighborhoodInclusion : Spec (.of (OriginNeighborhood W)) ⟶ integralCurve W :=
  PrincipalAffineRefinement.chart (integralCurveChart W 1) (originDenominator W)

instance originNeighborhoodInclusion_isOpenImmersion :
    IsOpenImmersion (originNeighborhoodInclusion W) := by
  unfold originNeighborhoodInclusion
  infer_instance

/-- The original zero section lifted to the actual parameter neighborhood. -/
def originNeighborhoodSection : Spec (.of R) ⟶ Spec (.of (OriginNeighborhood W)) :=
  Spec.map (CommRingCat.ofHom (originEvaluation W).toRingHom)

/-- The lifted section is precisely the original zero morphism. -/
@[reassoc] theorem originNeighborhoodSection_inclusion :
    originNeighborhoodSection W ≫ originNeighborhoodInclusion W = integralCurveZero W := by
  unfold originNeighborhoodSection originNeighborhoodInclusion PrincipalAffineRefinement.chart
  rw [← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (originEvaluation W).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (Coordinate W 1) (OriginNeighborhood W)))) ≫ _ = _
  rw [← Spec.map_comp]
  have he : (originEvaluation W).toRingHom.comp
      (algebraMap (Coordinate W 1) (OriginNeighborhood W)) =
        (chartInfinityEvaluation (S := R) W).toRingHom :=
    RingHom.ext (originEvaluation_restrict W)
  change Spec.map (CommRingCat.ofHom ((originEvaluation W).toRingHom.comp
    (algebraMap (Coordinate W 1) (OriginNeighborhood W)))) ≫ _ = _
  rw [he]
  rfl

/-- The parameter neighborhood and original affine chart cover every point of the cubic. -/
theorem originNeighborhood_affine_cover (x : integralCurve W) :
    x ∈ Set.range (originNeighborhoodInclusion W) ∨
      x ∈ Set.range (integralCurveChart W 2) := by
  rcases integralCurve_yz_cover W x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · by_cases hz : coord W 1 2 ∈ y.asIdeal
    · left
      apply PrincipalAffineRefinement.mem_range_chart
      exact originDenominator_notMem_of_z_mem W y hz
    · right
      have hy : y ∈ Set.range (PrincipalAffineRefinement.inclusion (coord W 1 2)) := by
        rw [PrincipalAffineRefinement.range_inclusion]
        exact hz
      obtain ⟨q, hq⟩ := hy
      refine ⟨Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) q, ?_⟩
      exact (congrArg (fun f ↦ f q) (integralCurve_output_transition W 1 2)).trans
        (congrArg (integralCurveChart W 1) hq)
  · exact Or.inr ⟨z, rfl⟩

end FLT.Mazur.WeierstrassIntegralChart
