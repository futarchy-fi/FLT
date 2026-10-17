/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAffineOpenAction
public import FLT.Mazur.PolygonCompleteIdentityActionLocalGluing
public import FLT.Mazur.PolygonCompleteMarkingSpecialization

/-!
# Coverage by actual original action neighborhoods

Every input outside the smooth open comes from the original order-zero input.
The previously constructed affine lifts therefore supply local actions at all
remaining points, with the entire original input scheme structure retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "j" => completeIdentityFiniteInput K n h 0 0
local notation "c" => completePointToIntegralCubic K n h 0
local notation "a" => completeIdentityActionTarget K n h 0

/-- The actual order-zero input has precisely the base-change image on original points. -/
theorem completeIdentityOriginalClosedInput_range :
    Set.range (j) = ((s) ≫ (π)) ⁻¹' Set.range (baseToSeries K 0) := by
  have hp := completeIdentityFiniteInput_base_isPullback K n h 0 0
  rw [← hp.isoPullback_hom_fst]
  change Set.range ((pullback.fst ((s) ≫ (π)) (baseToSeries K 0)) ∘
    hp.isoPullback.hom) = _
  exact (hp.isoPullback.hom.homeomorph.surjective.range_comp _).trans
    (Scheme.Pullback.range_fst _ _)

/-- Every nonsmooth original input lifts to the unchanged original order-zero input. -/
theorem completeIdentityOriginalClosedInput_of_not_smooth (x : P)
    (hx : x ∉ completeIdentityActionSmoothOpen K n h) : x ∈ Set.range (j) := by
  have ht : PowerSeries.X ∈ ((π) ((s) x)).asIdeal := by
    by_contra ht
    exact hx (complete_mem_smoothLocus_of_parameter_notMem K n h ((s) x) ht)
  have hb : (π) ((s) x) = IsLocalRing.closedPoint (PowerSeries K) := by
    apply PrimeSpectrum.ext
    symm
    change IsLocalRing.maximalIdeal (PowerSeries K) = ((π) ((s) x)).asIdeal
    apply Ideal.IsMaximal.eq_of_le inferInstance ((π) ((s) x)).isPrime.ne_top
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_le_iff_mem]
    exact ht
  rw [completeIdentityOriginalClosedInput_range]
  exact ⟨stageBasePoint K 0, (baseToSeries_stageBasePoint K 0).trans hb.symm⟩

/-- Every original input has an actual open neighborhood carrying the prescribed action. -/
theorem completeIdentityOriginalLocalLift_exists (x : P) :
    ∃ (U : (P).Opens) (F : U.toScheme ⟶ exactVeroneseProj K n h),
      x ∈ U ∧ F ≫ (c) = U.ι ≫ (a) := by
  by_cases hx : x ∈ completeIdentityActionSmoothOpen K n h
  · exact ⟨completeIdentityActionSmoothOpen K n h, completeIdentityActionSmoothLift K n h,
      hx, completeIdentityActionSmoothLift_contraction K n h⟩
  · obtain ⟨z, rfl⟩ := completeIdentityOriginalClosedInput_of_not_smooth K n h x hx
    obtain ⟨U, F, hz, hF⟩ := completeIdentityAffineOpenLift_exists K n h z
    exact ⟨U.1, F, hz, hF⟩

end FLT.Mazur.PolygonInfinitesimalStages
