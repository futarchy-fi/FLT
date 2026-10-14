/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginPunctureIntersection
public import FLT.Mazur.WeierstrassOriginIdealAffine

/-!
# The original affine chart is the complement of the origin

The parameter-ring augmentation and the exact puncture intersection identify the
whole topological complement of the original origin over arbitrary base rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- In the original parameter neighborhood, the actual origin is exactly x = 0. -/
theorem originNeighborhoodSection_range :
    Set.range (originNeighborhoodSection W) =
      {p | originCoordinate W 0 ∈ p.asIdeal} := by
  have hs : Function.Surjective (originEvaluation W).toRingHom := by
    intro r
    exact ⟨algebraMap R (OriginNeighborhood W) r, (originEvaluation W).commutes r⟩
  change Set.range (PrimeSpectrum.comap (originEvaluation W).toRingHom) = _
  rw [range_comap_of_surjective _ _ hs, originEvaluation_kernel]
  ext p
  change Ideal.span {originCoordinate W 0} ≤ p.asIdeal ↔ _
  exact Ideal.span_singleton_le_iff_mem (I := p.asIdeal) (x := originCoordinate W 0)

/-- A point of the cubic outside its affine chart belongs to the actual origin section. -/
theorem integralCurve_notMem_affine_iff (x : integralCurve W) :
    x ∉ Set.range (integralCurveChart W 2) ↔ x ∈ Set.range (integralCurveZero W) := by
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := (originNeighborhood_affine_cover W x).resolve_right hx
    have hp : originCoordinate W 0 ∈ p.asIdeal := by
      by_contra hn
      have hm : p ∈ (originNeighborhoodInclusion W) ⁻¹ᵁ
          (integralCurveChart W 2).opensRange := by
        rw [originNeighborhood_affine_preimage]
        change p ∈ Set.range (PrincipalAffineRefinement.inclusion (originCoordinate W 0))
        rw [PrincipalAffineRefinement.range_inclusion]
        exact hn
      exact hx hm
    have hr : p ∈ Set.range (originNeighborhoodSection W) := by
      rw [originNeighborhoodSection_range]
      exact hp
    obtain ⟨a, rfl⟩ := hr
    refine ⟨a, ?_⟩
    exact congrArg (fun f => f a) (originNeighborhoodSection_inclusion W).symm
  · rintro ⟨a, rfl⟩
    exact originSection_notMem_affine W a

/-- The original affine open is precisely the complement of the intrinsic origin ideal. -/
theorem integralCurve_affine_eq_origin_complement :
    (integralCurveChart W 2).opensRange = (integralCurveZero W).ker.support.compl := by
  ext x
  change x ∈ Set.range (integralCurveChart W 2) ↔
    x ∉ ((integralCurveZero W).ker.support : Set (integralCurve W))
  rw [Scheme.Hom.support_ker,
    (integralCurveZero W).isClosedEmbedding.isClosed_range.closure_eq]
  exact not_not.symm.trans (not_congr (integralCurve_notMem_affine_iff W x))

end FLT.Mazur.WeierstrassIntegralChart
