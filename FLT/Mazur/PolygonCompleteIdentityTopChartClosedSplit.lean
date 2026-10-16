/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartClosedLayer
public import FLT.Mazur.PolygonCompleteIdentityTopChartNodeReduction
public import FLT.Mazur.PolygonSmoothingSumRegular

/-!
# The actual chart closed fiber retracts onto the original split node

Both the section and retraction come from the unchanged original source
and comparison maps. The residual ideal is retained in full; no reducedness
or square-zero assertion about that ideal is made here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
  completeIdentityTopGraphReduction
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) (m + 1)
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "Q" => completeIdentityTopChartClosedFiber K n h m
local notation "t" => completeIdentityTopChartParameter K n h m
local notation "p" => completeIdentityTopChartSourceFunctions K n h m
local notation "q" => completeIdentityTopChartClosedQuotient K n h m
variable (hm : completeIdentityFiniteMulDefect K n h 0 m = 0)
local notation "r" => completeIdentityTopChartNodeReduction K n h m hm

/-- The literal closed quotient kills its original base parameter. -/
theorem completeIdentityTopChartClosedQuotient_parameter : (q) (t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The original source descends through the entire original node reduction kernel. -/
theorem completeIdentityTopChartClosedSource_kernel :
    RingHom.ker (topNodeReduction (R) m) ≤ RingHom.ker ((q).comp (p)) := by
  intro z hz
  obtain ⟨w, hw⟩ := (topNodeReduction_zero_iff (R) m z).mp hz
  change (q) ((p) z) = 0
  have hw' := hw.symm.trans (Algebra.smul_def (e) w)
  rw [hw', map_mul, completeIdentityTopChartSourceFunctions_parameter,
    map_mul, completeIdentityTopChartClosedQuotient_parameter, zero_mul]

/-- The original node sits inside the full chart closed fiber via its actual source. -/
def completeIdentityTopChartClosedSection : (N) →+* (Q) :=
  (topNodeReduction (R) m).liftOfSurjective (topNodeReduction_surjective (R) m)
    ⟨(q).comp (p), completeIdentityTopChartClosedSource_kernel K n h m⟩

/-- Every original node lift gives the same actual source section. -/
theorem completeIdentityTopChartClosedSection_reduction (z : B) :
    completeIdentityTopChartClosedSection K n h m (topNodeReduction (R) m z) =
      (q) ((p) z) :=
  (topNodeReduction (R) m).liftOfSurjective_comp_apply
    (topNodeReduction_surjective (R) m) _ z

/-- The actual whole-chart node reduction factors through its literal closed fiber. -/
def completeIdentityTopChartClosedReduction : (Q) →+* (N) :=
  Ideal.Quotient.lift _ (r) (by
    change Ideal.span {(t)} ≤ RingHom.ker (r)
    rw [Ideal.span_singleton_le_iff_mem]
    exact completeIdentityTopChartNodeReduction_parameter K n h m hm)

/-- The factorization retains the original reduction on every chart function. -/
theorem completeIdentityTopChartClosedReduction_mk (z : Γ((H), ⊤)) :
    completeIdentityTopChartClosedReduction K n h m hm ((q) z) = (r) z := rfl

/-- The original source is a right inverse to the actual closed-fiber node reduction. -/
theorem completeIdentityTopChartClosedSection_rightInverse :
    Function.RightInverse (completeIdentityTopChartClosedSection K n h m)
      (completeIdentityTopChartClosedReduction K n h m hm) := by
  intro z
  obtain ⟨w, rfl⟩ := topNodeReduction_surjective (R) m z
  rw [completeIdentityTopChartClosedSection_reduction,
    completeIdentityTopChartClosedReduction_mk, completeIdentityTopChartNodeReduction_source]

include hm in
/-- The source embeds the whole unchanged split node into the actual closed fiber. -/
theorem completeIdentityTopChartClosedSection_injective :
    Function.Injective (completeIdentityTopChartClosedSection K n h m) :=
  (completeIdentityTopChartClosedSection_rightInverse K n h m hm).injective

/-- The actual closed-fiber node reduction is surjective. -/
theorem completeIdentityTopChartClosedReduction_surjective :
    Function.Surjective (completeIdentityTopChartClosedReduction K n h m hm) :=
  (completeIdentityTopChartClosedSection_rightInverse K n h m hm).surjective

/-- The actual fiber reduction retains the original outgoing node coordinate. -/
theorem completeIdentityTopChartClosedReduction_left :
    completeIdentityTopChartClosedReduction K n h m hm
      ((q) (completeIdentityTopChartSourceX K n h m)) = leftCoordinate (0 : R) := by
  change completeIdentityTopChartClosedReduction K n h m hm ((q) ((p) (leftCoordinate (e)))) = _
  rw [completeIdentityTopChartClosedReduction_mk,
    completeIdentityTopChartNodeReduction_source, topNodeReduction_left]

/-- The actual fiber reduction retains the original incoming node coordinate. -/
theorem completeIdentityTopChartClosedReduction_right :
    completeIdentityTopChartClosedReduction K n h m hm
      ((q) (completeIdentityTopChartSourceY K n h m)) = rightCoordinate (0 : R) := by
  change completeIdentityTopChartClosedReduction K n h m hm ((q) ((p) (rightCoordinate (e)))) = _
  rw [completeIdentityTopChartClosedReduction_mk,
    completeIdentityTopChartNodeReduction_source, topNodeReduction_right]

/-- All remaining closed-fiber node socle lies in the actual retraction kernel. -/
theorem completeIdentityTopChartClosedSocle_reduction (z : Q)
    (hx : (q) (completeIdentityTopChartSourceX K n h m) * z = 0)
    (hy : (q) (completeIdentityTopChartSourceY K n h m) * z = 0) :
    completeIdentityTopChartClosedReduction K n h m hm z = 0 := by
  have hl := congrArg (completeIdentityTopChartClosedReduction K n h m hm) hx
  have hr := congrArg (completeIdentityTopChartClosedReduction K n h m hm) hy
  rw [map_mul, completeIdentityTopChartClosedReduction_left, map_zero] at hl
  rw [map_mul, completeIdentityTopChartClosedReduction_right, map_zero] at hr
  apply (branchSum_regular (0 : R)).left
  change (leftCoordinate (0 : R) + rightCoordinate (0 : R)) *
    completeIdentityTopChartClosedReduction K n h m hm z = _
  simp only [add_mul, hl, hr, add_zero, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
