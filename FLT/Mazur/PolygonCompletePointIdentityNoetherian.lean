/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityAffineQuotient
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# Noetherianity of the actual finite identity target

The cubic origin ring is a localization of the original polynomial quotient.
Its chosen affine identity neighborhood therefore has a Noetherian section ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] [IsNoetherianRing R] (W : WeierstrassCurve R)

/-- The original cubic origin neighborhood is Noetherian over a Noetherian base. -/
theorem originNeighborhood_isNoetherianRing : IsNoetherianRing (OriginNeighborhood W) := by
  let _ : IsNoetherianRing (Coordinate W 1) := inferInstance
  exact IsLocalization.isNoetherianRing (.powers (originDenominator W)) _ inferInstance

end FLT.Mazur.WeierstrassIntegralChart

namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointIdentityAffineOpen completePointToOrigin completePointOriginOpen
  completePointIdentityAffineSourceMarking completePointIdentityAffineTargetMarking
  completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "U" => completePointIdentityAffineOpen K n h i

/-- Noetherianity holds for the actual finite target chart, before localizing at a marking point. -/
theorem completePointIdentityAffine_isNoetherianRing :
    IsNoetherianRing Γ((U).toScheme, ⊤) := by
  let _ : IsNoetherianRing Γ(Spec (.of (PowerSeries K)), ⊤) :=
    isNoetherianRing_of_ringEquiv (PowerSeries K)
      (Scheme.ΓSpecIso (.of (PowerSeries K))).commRingCatIsoToRingEquiv.symm
  let _ := originNeighborhood_isNoetherianRing (W)
  let _ : IsAffine (U).toScheme := (completePointIdentityAffineOpen_spec K n h i).2.1
  let _ : IsLocallyNoetherian (Spec (.of (OriginNeighborhood (W)))) := inferInstance
  let _ : IsLocallyNoetherian (U).toScheme := inferInstance
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

end FLT.Mazur.PolygonInfinitesimalStages
