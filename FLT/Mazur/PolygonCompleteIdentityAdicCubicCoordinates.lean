/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicCubicPatches
public import FLT.Mazur.PolygonCompleteIdentityAdicRefinedKernel
public import FLT.Mazur.PolygonCompleteIdentityCubicCoordinates

/-!
# Exact specialization of the original complete cubic-action coordinates

The original complete coordinate homomorphism restricts to each refined
patch and then to the full adic relation. Arbitrary polynomial equations
are tested by literal parameter-power divisibility before specialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h m i j U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h m i j U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h m i j U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "C" k => completeIdentityCubicChartOpen K n h k
variable (k : Fin 3)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
  completeIdentityCubicChartOpen K n h k)

/-- Actual complete cubic functions restricted to the original complete affine patch. -/
def completeIdentityCubicPatchFunctions :
    Coordinate (E) k →+* Γ(completeIdentityActionLiftSpace K n h, (W).1) :=
  ((completeIdentityActionLiftSpace K n h).presheaf.map (homOfLE hC).op).hom.comp
    ((C k).topIso.hom.hom.comp (completeIdentityCubicFunctions K n h k))
local notation "F" => completeIdentityCubicPatchFunctions K n h m i j U k hC

/-- The unchanged adic specialization of all original cubic-action coordinate functions. -/
def completeIdentityAdicCubicFunctions :
    Coordinate (E) k →+* Γ(completeIdentityActionAdicChartSpace K n h m i j, (V).1) :=
  (p).hom.comp (F)
local notation "A" => completeIdentityAdicCubicFunctions K n h m i j U k hC

/-- The chosen cubic denominator stays normalized on the full original complete patch. -/
theorem completeIdentityCubicPatchFunctions_self : (F) (coord (E) k k) = 1 := by
  rw [coord_self, map_one]

/-- The full original adic coordinate map retains this normalization, including nilpotents. -/
theorem completeIdentityAdicCubicFunctions_self : (A) (coord (E) k k) = 1 := by
  rw [coord_self, map_one]

/-- The complete patch coordinates satisfy the original cubic before taking any quotient. -/
theorem completeIdentityCubicPatchFunctions_equation :
    ((E).map ((F).comp (algebraMap _ (Coordinate (E) k)))).toProjective.Equation
      (fun l ↦ (F) (coord (E) k l)) := by
  simpa only [WeierstrassCurve.map_map, Function.comp_def] using
    (coord_equation (E) k).map (F)

/-- The actual entire adic relation retains the original cubic polynomial equation. -/
theorem completeIdentityAdicCubicFunctions_equation :
    ((E).map ((A).comp (algebraMap _ (Coordinate (E) k)))).toProjective.Equation
      (fun l ↦ (A) (coord (E) k l)) := by
  simpa only [WeierstrassCurve.map_map, Function.comp_def] using
    (coord_equation (E) k).map (A)

local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)
variable (hU : (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
  completeIdentityAdicNodeNeighborhood K n h m i j)
include hU

/-- Exact adic cubic equations are parameter-power divisibilities in the complete ring. -/
theorem completeIdentityAdicCubicFunctions_eq_zero_iff (z : Coordinate (E) k) :
    (A) z = 0 ↔ (τ) ^ (m + 1) ∣ (F) z :=
  completeIdentityAdicRefinedPatch_equation_iff K n h m i j U hU ((F) z)

/-- An arbitrary complete representative of an original cubic function has an exact remainder. -/
theorem completeIdentityAdicCubicFunctions_remainder (z : Coordinate (E) k)
    (v : Γ(completeIdentityActionLiftSpace K n h, (W).1)) (hv : (p) v = (A) z) :
    (τ) ^ (m + 1) ∣ v - (F) z :=
  (completeIdentityAdicRefinedPatch_eq_iff K n h m i j U hU v ((F) z)).mp hv

end FLT.Mazur.PolygonInfinitesimalStages
