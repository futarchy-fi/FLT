/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstLocalSocleMembership
public import FLT.Mazur.AffineIdealNeighborhoodMembership

/-!
# The full original first-chart node socle vanishes

The actual local cubic comparisons detect membership in the unchanged
ambient graph-plus-parameter ideal on a covering family. Consequently the
original comparison kernel vanishes, including all its nilpotent elements.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "e" => parameter K[T;T⁻¹] 1
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "f" => completeIdentityFirstChartClosedAmbientMap K n h
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h
local notation "q" => completeIdentityFirstChartClosedQuotient K n h
local notation "x" => completeIdentityFirstChartSourceX K n h
local notation "y" => completeIdentityFirstChartSourceY K n h

/-- Full local membership descends to the original graph-plus-parameter ideal. -/
theorem completeIdentityFirstChartAmbientSocle_vanishing (z : Γ((R), ⊤))
    (hx : (s) (leftCoordinate (e)) * z ∈ (J))
    (hy : (s) (rightCoordinate (e)) * z ∈ (J)) : z ∈ (J) := by
  apply AffineIdealNeighborhoodMembership.mem_of_neighborhoods
  intro p
  obtain ⟨U, hp⟩ := completeIdentityAdicAmbientPatch_cover K n h 1 0 0 p
  exact ⟨completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U, hp,
    completeIdentityFirstLocalSocle_mem K n h U z hx hy⟩

/-- The unchanged original comparison has no remaining kernel. -/
theorem completeIdentityFirstChartNodeKernel_eq_bot :
    completeIdentityFirstChartNodeKernel K n h = ⊥ :=
  (completeIdentityFirstChartNodeKernel_eq_bot_iff_ambientSocle K n h).mpr
    (completeIdentityFirstChartAmbientSocle_vanishing K n h)

/-- The literal original closed fiber has no common source-coordinate annihilator. -/
theorem completeIdentityFirstChartClosedSocle_eq_zero
    (z : completeIdentityFirstChartClosedFiber K n h)
    (hx : (q) (x) * z = 0) (hy : (q) (y) * z = 0) : z = 0 :=
  (completeIdentityFirstChartNodeKernel_eq_bot_iff_closedSocle K n h).mp
    (completeIdentityFirstChartNodeKernel_eq_bot K n h) z hx hy

/-- The original finite graph comparison is an isomorphism onto the entire original chart. -/
theorem completeIdentityFirstGraphToChart_isIso :
    IsIso (completeIdentityFirstGraphToChart K n h) :=
  completeIdentityFirstGraphToChart_isIso_of_kernel K n h
    (completeIdentityFirstChartNodeKernel_eq_bot K n h)

end FLT.Mazur.PolygonInfinitesimalStages
