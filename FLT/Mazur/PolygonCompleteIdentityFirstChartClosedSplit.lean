/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartClosedLayer
public import FLT.Mazur.PolygonCompleteIdentityFirstChartSourceFunctions
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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "Q" => completeIdentityFirstChartClosedFiber K n h
local notation "t" => completeIdentityFirstChartParameter K n h
local notation "p" => completeIdentityFirstChartSourceFunctions K n h
local notation "q" => completeIdentityFirstChartClosedQuotient K n h
local notation "r" => completeIdentityFirstChartNodeReduction K n h

/-- The literal closed quotient kills its original base parameter. -/
theorem completeIdentityFirstChartClosedQuotient_parameter : (q) (t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The original source descends through the entire original node reduction kernel. -/
theorem completeIdentityFirstChartClosedSource_kernel :
    RingHom.ker (firstNodeReduction (R)) ≤ RingHom.ker ((q).comp (p)) := by
  intro z hz
  obtain ⟨w, hw⟩ := (firstNodeReduction_zero_iff (R) z).mp hz
  change (q) ((p) z) = 0
  have hw' := hw.symm.trans (Algebra.smul_def (e) w)
  rw [hw', map_mul, completeIdentityFirstChartSourceFunctions_parameter,
    map_mul, completeIdentityFirstChartClosedQuotient_parameter, zero_mul]

/-- The original node sits inside the full chart closed fiber via its actual source. -/
def completeIdentityFirstChartClosedSection : (N) →+* (Q) :=
  (firstNodeReduction (R)).liftOfSurjective (firstNodeReduction_surjective (R))
    ⟨(q).comp (p), completeIdentityFirstChartClosedSource_kernel K n h⟩

/-- Every original node lift gives the same actual source section. -/
theorem completeIdentityFirstChartClosedSection_reduction (z : B) :
    completeIdentityFirstChartClosedSection K n h (firstNodeReduction (R) z) =
      (q) ((p) z) :=
  (firstNodeReduction (R)).liftOfSurjective_comp_apply
    (firstNodeReduction_surjective (R)) _ z

/-- The actual whole-chart node reduction factors through its literal closed fiber. -/
def completeIdentityFirstChartClosedReduction : (Q) →+* (N) :=
  Ideal.Quotient.lift _ (r) (by
    change Ideal.span {(t)} ≤ RingHom.ker (r)
    rw [Ideal.span_singleton_le_iff_mem]
    exact completeIdentityFirstChartNodeReduction_parameter K n h)

/-- The factorization retains the original reduction on every chart function. -/
theorem completeIdentityFirstChartClosedReduction_mk (z : Γ((H), ⊤)) :
    completeIdentityFirstChartClosedReduction K n h ((q) z) = (r) z := rfl

/-- The original source is a right inverse to the actual closed-fiber node reduction. -/
theorem completeIdentityFirstChartClosedSection_rightInverse :
    Function.RightInverse (completeIdentityFirstChartClosedSection K n h)
      (completeIdentityFirstChartClosedReduction K n h) := by
  intro z
  obtain ⟨w, rfl⟩ := firstNodeReduction_surjective (R) z
  rw [completeIdentityFirstChartClosedSection_reduction,
    completeIdentityFirstChartClosedReduction_mk, completeIdentityFirstChartNodeReduction_source]

/-- The source embeds the whole unchanged split node into the actual closed fiber. -/
theorem completeIdentityFirstChartClosedSection_injective :
    Function.Injective (completeIdentityFirstChartClosedSection K n h) :=
  (completeIdentityFirstChartClosedSection_rightInverse K n h).injective

/-- The actual closed-fiber node reduction is surjective. -/
theorem completeIdentityFirstChartClosedReduction_surjective :
    Function.Surjective (completeIdentityFirstChartClosedReduction K n h) :=
  (completeIdentityFirstChartClosedSection_rightInverse K n h).surjective

/-- The actual fiber reduction retains the original outgoing node coordinate. -/
theorem completeIdentityFirstChartClosedReduction_left :
    completeIdentityFirstChartClosedReduction K n h
      ((q) (completeIdentityFirstChartSourceX K n h)) = leftCoordinate (0 : R) := by
  change completeIdentityFirstChartClosedReduction K n h ((q) ((p) (leftCoordinate (e)))) = _
  rw [completeIdentityFirstChartClosedReduction_mk,
    completeIdentityFirstChartNodeReduction_source, firstNodeReduction_left]

/-- The actual fiber reduction retains the original incoming node coordinate. -/
theorem completeIdentityFirstChartClosedReduction_right :
    completeIdentityFirstChartClosedReduction K n h
      ((q) (completeIdentityFirstChartSourceY K n h)) = rightCoordinate (0 : R) := by
  change completeIdentityFirstChartClosedReduction K n h ((q) ((p) (rightCoordinate (e)))) = _
  rw [completeIdentityFirstChartClosedReduction_mk,
    completeIdentityFirstChartNodeReduction_source, firstNodeReduction_right]

/-- All remaining closed-fiber node socle lies in the actual retraction kernel. -/
theorem completeIdentityFirstChartClosedSocle_reduction (z : Q)
    (hx : (q) (completeIdentityFirstChartSourceX K n h) * z = 0)
    (hy : (q) (completeIdentityFirstChartSourceY K n h) * z = 0) :
    completeIdentityFirstChartClosedReduction K n h z = 0 := by
  have hl := congrArg (completeIdentityFirstChartClosedReduction K n h) hx
  have hr := congrArg (completeIdentityFirstChartClosedReduction K n h) hy
  rw [map_mul, completeIdentityFirstChartClosedReduction_left, map_zero] at hl
  rw [map_mul, completeIdentityFirstChartClosedReduction_right, map_zero] at hr
  apply (branchSum_regular (0 : R)).left
  change (leftCoordinate (0 : R) + rightCoordinate (0 : R)) *
    completeIdentityFirstChartClosedReduction K n h z = _
  simp only [add_mul, hl, hr, add_zero, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
