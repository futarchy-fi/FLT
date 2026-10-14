/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointResidueNeighborhood
public import FLT.Mazur.PolygonCompletePointTorusNeighborhood
public import FLT.Mazur.PolygonClosedCubicSmoothTorus
public import FLT.Mazur.PolygonCompleteClosedSpecialization
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange

/-!
# The original contraction is unchanged over the entire smooth cubic

Every smooth cubic point is covered: nonzero-parameter residues use the
original generic comparison; closed residues use the complete retained torus.
The resulting isomorphism is the restriction of the unchanged original map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => integralCurveStructure (W)
local notation "b" => completePointCubicOriginalBase K n h i
local notation "j" => completePointCubicClosedInclusion K n h i

/-- The original closed cubic occupies exactly the closed coefficient fiber. -/
theorem completePointCubicClosedInclusion_range :
    Set.range (j) = (b) ⁻¹' {IsLocalRing.closedPoint (PowerSeries K)} := by
  change Set.range (pullback.fst (c) (completeClosedBase K ≫ (S₀).toSpecΓ)) = _
  rw [Scheme.Pullback.range_fst,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, completeClosedBase_range,
    Set.image_singleton]
  ext y
  change (c) y = (S₀).toSpecΓ (IsLocalRing.closedPoint (PowerSeries K)) ↔
    inv (S₀).toSpecΓ ((c) y) = IsLocalRing.closedPoint (PowerSeries K)
  constructor
  · intro hy
    rw [hy]
    exact congrArg (fun v : S₀ ⟶ S₀ ↦ v (IsLocalRing.closedPoint (PowerSeries K)))
      (IsIso.hom_inv_id (S₀).toSpecΓ)
  · intro hy
    apply (inv (S₀).toSpecΓ).isOpenEmbedding.injective
    rw [hy]
    exact (congrArg (fun v : S₀ ⟶ S₀ ↦ v (IsLocalRing.closedPoint (PowerSeries K)))
      (IsIso.hom_inv_id (S₀).toSpecΓ)).symm

/-- Flatness identifies the actual closed cubic's smooth open with the original smooth open. -/
theorem completePointCubicClosedInclusion_preimage_smooth :
    (j) ⁻¹ᵁ (c).smoothLocus = (closedPointCubicOver K n h i).hom.smoothLocus := by
  exact Scheme.Hom.preimage_smoothLocus_baseChange (c)
    (completeClosedBase K ≫ (S₀).toSpecΓ)

/-- The original complete-base morphism is unchanged on the entire smooth cubic. -/
theorem completePointToIntegralCubic_smooth_isIso : IsIso ((g) ∣_ (c).smoothLocus) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro y hy
  by_cases ht : PowerSeries.X ∈ ((b) y).asIdeal
  · have hb : (b) y = IsLocalRing.closedPoint (PowerSeries K) := by
      apply PrimeSpectrum.ext
      symm
      change IsLocalRing.maximalIdeal (PowerSeries K) = ((b) y).asIdeal
      apply Ideal.IsMaximal.eq_of_le inferInstance ((b) y).isPrime.ne_top
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_le_iff_mem]
      exact ht
    have hr : y ∈ Set.range (j) := by
      rw [completePointCubicClosedInclusion_range]
      exact hb
    obtain ⟨z, rfl⟩ := hr
    have hz : z ∈ (closedPointCubicTorus K n h i).opensRange := by
      rw [← closedPointCubic_smoothLocus_eq_torus,
        ← completePointCubicClosedInclusion_preimage_smooth]
      exact hy
    exact completePointToIntegralCubic_exists_isIso_closedTorus K n h i z hz
  · exact completePointToIntegralCubic_exists_isIso_parameter_notMem K n h i y ht

/-- The entire inverse image of the smooth cubic, with the actual contraction as forward map. -/
def completePointSmoothCubicIso :
    ((g) ⁻¹ᵁ (c).smoothLocus).toScheme ≅ (c).smoothLocus.toScheme := by
  let _ := completePointToIntegralCubic_smooth_isIso K n h i
  exact asIso ((g) ∣_ (c).smoothLocus)

/-- The constructed smooth comparison retains the original global contraction. -/
@[reassoc] theorem completePointSmoothCubicIso_inclusion :
    (completePointSmoothCubicIso K n h i).hom ≫ (c).smoothLocus.ι =
      ((g) ⁻¹ᵁ (c).smoothLocus).ι ≫ (g) := morphismRestrict_ι _ _

end FLT.Mazur.PolygonInfinitesimalStages
