/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginPunctureGeometry
public import FLT.Mazur.WeierstrassOriginIdealSheaf

/-!
# The puncture is the actual two-chart intersection

The parameter puncture satisfies the scheme pullback universal property for
the original parameter neighborhood and affine chart. Thus its ring is the
ring of the full overlap needed to glue the actual dual-ideal sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual affine chart in the infinity chart is exactly the original z-basic open. -/
theorem originInfinity_affine_mem_iff (x : chartScheme W 1) :
    integralCurveChart W 1 x ∈ Set.range (integralCurveChart W 2) ↔
      coord W 1 2 ∉ x.asIdeal := by
  have hi : integralCurveChart W 1 x ∈ Set.range (integralCurveChart W 2) ↔
      x ∈ Set.range (overlapInclusion W 1 2) := by
    constructor
    · intro hx
      have hm : integralCurveChart W 1 x ∈
          Set.range (overlapInclusion W 1 2 ≫ integralCurveChart W 1) := by
        rw [integralChartIntersection_range]
        exact ⟨⟨x, rfl⟩, hx⟩
      obtain ⟨y, hy⟩ := hm
      exact ⟨y, (integralCurveChart W 1).isOpenEmbedding.injective hy⟩
    · rintro ⟨y, rfl⟩
      have hm : (overlapInclusion W 1 2 ≫ integralCurveChart W 1) y ∈
          Set.range (overlapInclusion W 1 2 ≫ integralCurveChart W 1) := ⟨y, rfl⟩
      rw [integralChartIntersection_range] at hm
      exact hm.2
  rw [overlapInclusion, PrincipalAffineRefinement.range_inclusion] at hi
  exact hi

/-- The original z and parameter have the same vanishing locus on the actual neighborhood. -/
theorem originNeighborhood_z_mem_iff (p : PrimeSpectrum (OriginNeighborhood W)) :
    originCoordinate W 2 ∈ p.asIdeal ↔ originCoordinate W 0 ∈ p.asIdeal := by
  constructor
  · intro hz
    apply p.isPrime.mem_of_pow_mem 3
    rw [← originCoordinate_relation]
    exact p.asIdeal.mul_mem_right _ hz
  · intro ht
    have hle : Ideal.span {originCoordinate W 0} ≤ p.asIdeal :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht)
    exact hle (originCoordinate_z_mem_parameter W)

/-- The full affine-chart preimage is the actual parameter puncture. -/
theorem originNeighborhood_affine_preimage :
    originNeighborhoodInclusion W ⁻¹ᵁ (integralCurveChart W 2).opensRange =
      (PrincipalAffineRefinement.inclusion (originCoordinate W 0)).opensRange := by
  ext p
  change integralCurveChart W 1
    (Spec.map (CommRingCat.ofHom (algebraMap (Coordinate W 1) (OriginNeighborhood W))) p) ∈
      Set.range (integralCurveChart W 2) ↔
        p ∈ Set.range (PrincipalAffineRefinement.inclusion (originCoordinate W 0))
  rw [originInfinity_affine_mem_iff, PrincipalAffineRefinement.range_inclusion]
  change originCoordinate W 2 ∉ p.asIdeal ↔ originCoordinate W 0 ∉ p.asIdeal
  exact not_congr (originNeighborhood_z_mem_iff W p)

/-- The puncture is the actual scheme pullback of the two original chart inclusions. -/
theorem originPuncture_isPullback :
    IsPullback (PrincipalAffineRefinement.inclusion (originCoordinate W 0))
      (Spec.map (CommRingCat.ofHom (originPunctureAffine W).toRingHom))
      (originNeighborhoodInclusion W) (integralCurveChart W 2) :=
  (IsOpenImmersion.isPullback _ _ _ _ (originPuncture_inclusion W)
    (originNeighborhood_affine_preimage W)).flip

/-- The original puncture ring represents the full intersection, with both projections. -/
def originPunctureIntersectionIso : Spec (.of (OriginPuncture W)) ≅
    pullback (originNeighborhoodInclusion W) (integralCurveChart W 2) :=
  (originPuncture_isPullback W).isoPullback

/-- The first intersection projection is the actual original localization inclusion. -/
@[reassoc] theorem originPunctureIntersectionIso_fst :
    (originPunctureIntersectionIso W).hom ≫ pullback.fst _ _ =
      PrincipalAffineRefinement.inclusion (originCoordinate W 0) :=
  (originPuncture_isPullback W).isoPullback_hom_fst

/-- The second projection is the original affine coordinate map used in every pole bound. -/
@[reassoc] theorem originPunctureIntersectionIso_snd :
    (originPunctureIntersectionIso W).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (originPunctureAffine W).toRingHom) :=
  (originPuncture_isPullback W).isoPullback_hom_snd

end FLT.Mazur.WeierstrassIntegralChart
