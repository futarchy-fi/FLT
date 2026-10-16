/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePrincipalEquationLift
public import FLT.Mazur.PolygonCompleteIdentityFirstCubicFractionErrors

/-!
# Lift original cubic fraction equations to the complete ambient ring

The actual cubic coordinate homomorphism is retained. Clearing a local fraction
gives parameter-square divisibility after a power of the lifted denominator;
no multiplicativity of chosen lifts or cancellation of either power is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Y" => completeIdentityActionLiftSpace K n h
local notation "B" => Ring K[T;T⁻¹] 1
local notation "P" => completeIdentityFirstFourCoordinateMap K n h
local notation "L" => completeIdentityAdicAmbientLift K n h 1 0 0 U
local notation "π" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)
variable (d : MvPolynomial (Fin 2 ⊕ Fin 2) (Ring K[T;T⁻¹] 1))
variable (hd : (completeIdentityActionAdicChartSpace K n h 1 0 0).basicOpen
  (completeIdentityFirstFourCoordinateMap K n h d) ≤
    (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1)
local notation "ρ" => completeIdentityFirstFractionRestriction K n h d
local notation "res" => completeIdentityFirstFractionPatchRestriction K n h U d hd

/-- Restricting a chosen complete lift retains the original global function on this basic open. -/
theorem completeIdentityFirstFractionLift_spec (z : Γ((R), ⊤)) :
    (res) ((π) ((L) z)) = (ρ) z := by
  rw [completeIdentityAdicAmbientLift_spec]
  change ((R).presheaf.map (homOfLE le_top).op ≫
    (R).presheaf.map (homOfLE hd).op) z = (ρ) z
  rw [← Functor.map_comp]
  rfl

variable (hU : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityAdicNodeNeighborhood K n h 1 0 0)
include hU

/-- The exact complete-ring criterion for an equation on the original fraction chart. -/
theorem completeIdentityFirstFractionLift_equation_iff (z : Γ((Y), (W).1)) :
    (res) ((π) z) = 0 ↔ ∃ r : ℕ, (τ) ^ 2 ∣ (L) ((P) d) ^ r * z :=
  AffinePrincipalEquationLift.equation_iff (V) (π).hom (τ) 2
    (completeIdentityAdicRefinedPatch_kernel K n h 1 0 0 U hU)
    ((P) d) hd ((L) ((P) d)) (completeIdentityAdicAmbientLift_spec K n h 1 0 0 U _) z

local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
variable (k : Fin 3)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityCubicChartOpen K n h k)
local notation "A" => completeIdentityAdicCubicFunctions K n h 1 0 0 U k hC
local notation "F" => completeIdentityCubicPatchFunctions K n h 1 0 0 U k hC

/-- The actual cubic numerator equation lifts with denominator and parameter powers retained. -/
theorem completeIdentityFirstCubicFraction_remainder (z : Coordinate (E) k)
    (r : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin 2) (B))
    (hp : (res) ((A) z) * (ρ) ((P) d) ^ r = (ρ) ((P) p)) :
    ∃ v : ℕ, (τ) ^ 2 ∣ (L) ((P) d) ^ v *
      ((F) z * (L) ((P) d) ^ r - (L) ((P) p)) := by
  apply (completeIdentityFirstFractionLift_equation_iff K n h U d hd hU _).mp
  simp only [map_sub, map_mul, map_pow, completeIdentityFirstFractionLift_spec]
  exact sub_eq_zero.mpr hp

end FLT.Mazur.PolygonInfinitesimalStages
