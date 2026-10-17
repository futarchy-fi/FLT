/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopLocalSocleMembership
public import FLT.Mazur.AffineIdealNeighborhoodMembership
public import FLT.Mazur.PolygonCompleteIdentityTopGraphChartFlat

/-!
# The full original higher-chart node socle vanishes

The actual local cubic comparisons detect membership in the unchanged
ambient graph-plus-parameter ideal on a covering family. Consequently the
original comparison kernel vanishes, including all its nilpotent elements,
whenever the preceding original law holds.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (hm : completeIdentityFiniteMulDefect K n h 0 m = 0)
include hm
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "s" => completeIdentityTopAmbientSourceFunctions K n h m
local notation "f" => completeIdentityTopChartClosedAmbientMap K n h m
local notation "J" => completeIdentityTopChartClosedAmbientIdeal K n h m
local notation "q" => completeIdentityTopChartClosedQuotient K n h m
local notation "x" => completeIdentityTopChartSourceX K n h m
local notation "y" => completeIdentityTopChartSourceY K n h m

/-- Full local membership descends to the original graph-plus-parameter ideal. -/
theorem completeIdentityTopChartAmbientSocle_vanishing (z : Γ((R), ⊤))
    (hx : (s) (leftCoordinate (e)) * z ∈ (J))
    (hy : (s) (rightCoordinate (e)) * z ∈ (J)) : z ∈ (J) := by
  apply AffineIdealNeighborhoodMembership.mem_of_neighborhoods
  intro p
  obtain ⟨U, hp⟩ := completeIdentityAdicAmbientPatch_cover K n h (m + 1) 0 0 p
  exact ⟨completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U, hp,
    completeIdentityTopLocalSocle_mem K n h m hm U z hx hy⟩

/-- The unchanged original comparison has no remaining kernel. -/
theorem completeIdentityTopChartNodeKernel_eq_bot :
    completeIdentityTopChartNodeKernel K n h m = ⊥ :=
  (completeIdentityTopChartNodeKernel_eq_bot_iff_ambientSocle K n h m).mpr
    (completeIdentityTopChartAmbientSocle_vanishing K n h m hm)

/-- The literal original closed fiber has no common source-coordinate annihilator. -/
theorem completeIdentityTopChartClosedSocle_eq_zero
    (z : completeIdentityTopChartClosedFiber K n h m)
    (hx : (q) (x) * z = 0) (hy : (q) (y) * z = 0) : z = 0 :=
  (completeIdentityTopChartNodeKernel_eq_bot_iff_closedSocle K n h m).mp
    (completeIdentityTopChartNodeKernel_eq_bot K n h m hm) z hx hy

/-- The original finite graph comparison is an isomorphism onto the entire original chart. -/
theorem completeIdentityTopGraphToChart_isIso :
    IsIso (completeIdentityTopGraphToChart K n h m) :=
  completeIdentityTopGraphToChart_isIso_of_kernel K n h m
    (completeIdentityTopChartNodeKernel_eq_bot K n h m hm)

/-- The graph is flat over the unchanged original base after the preceding law. -/
theorem completeIdentityTopGraphOriginalScalars_flat :
    (completeIdentityTopGraphOriginalScalars K n h 0 m).Flat :=
  completeIdentityTopGraphOriginalScalars_flat_of_kernel K n h m
    (completeIdentityTopChartNodeKernel_eq_bot K n h m hm)

end FLT.Mazur.PolygonInfinitesimalStages
