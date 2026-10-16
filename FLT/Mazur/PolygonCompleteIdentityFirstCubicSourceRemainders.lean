/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstFractionLifts
public import FLT.Mazur.PolygonCompleteIdentityFirstCompleteErrors

/-!
# Complete cross-equations for the actual cubic function and scaled source

Lift the explicit coefficients of the original cubic fraction error to the
complete ring on the same patch. A denominator power clears the local equation;
the remainder is divisible by the actual smoothing parameter squared.
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
local notation "B" => Ring K[T;T⁻¹] 1
local notation "P" => completeIdentityFirstFourCoordinateMap K n h
local notation "S" => completeIdentityFirstFourScaledMap K
local notation "L" => completeIdentityAdicAmbientLift K n h 1 0 0 U
local notation "π" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "s" => completeIdentityFirstCompleteSource K n h U
local notation "D" => completeIdentityFirstCompleteError K n h U
local notation "dx" => completeIdentityFirstAmbientError K n h
local notation "x" => leftCoordinate (parameter K 1)
local notation "y" => rightCoordinate (parameter K 1)
local notation "lc" => completeIdentityFirstFourLeftCoefficient K n h
local notation "rc" => completeIdentityFirstFourRightCoefficient K n h
local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
variable (k : Fin 3)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityCubicChartOpen K n h k)
local notation "A" => completeIdentityAdicCubicFunctions K n h 1 0 0 U k hC
local notation "F" => completeIdentityCubicPatchFunctions K n h 1 0 0 U k hC
variable (d : MvPolynomial (Fin 2 ⊕ Fin 2) (Ring K[T;T⁻¹] 1))
variable (hd : (completeIdentityActionAdicChartSpace K n h 1 0 0).basicOpen
  (completeIdentityFirstFourCoordinateMap K n h d) ≤
    (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1)
local notation "ρ" => completeIdentityFirstFractionRestriction K n h d
local notation "res" => completeIdentityFirstFractionPatchRestriction K n h U d hd

/-- The original complete coordinate error retains its value on the exact fraction chart. -/
theorem completeIdentityFirstCubicFraction_completeError_spec
    (z : ChartRing (parameter K 1)) : (res) ((π) ((D) z)) = (ρ) ((dx) z) := by
  rw [completeIdentityFirstCompleteError_spec]
  change ((R).presheaf.map (homOfLE le_top).op ≫
    (R).presheaf.map (homOfLE hd).op) ((dx) z) = (ρ) ((dx) z)
  rw [← Functor.map_comp]
  rfl

/-- The actual source cross-equation lifts with explicit coefficients of the original D(x), D(y). -/
theorem completeIdentityFirstCubicFraction_source_remainder
    (hU : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
      completeIdentityAdicNodeNeighborhood K n h 1 0 0)
    (z : Coordinate (E) k) (r : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin 2) (B))
    (hp : (res) ((A) z) * (ρ) ((P) d) ^ r = (ρ) ((P) p)) :
    ∃ v : ℕ, (τ) ^ 2 ∣ (L) ((P) d) ^ v *
      ((F) z * (s) ((S) d) ^ r - (s) ((S) p) -
        (((L) ((lc) p) - (F) z * (L) ((lc) (d ^ r))) * (D) (x) +
          ((L) ((rc) p) - (F) z * (L) ((rc) (d ^ r))) * (D) (y))) := by
  apply (completeIdentityFirstFractionLift_equation_iff K n h U d hd hU _).mp
  simp only [completeIdentityFirstCompleteSource, map_sub, map_add, map_mul, map_pow,
    completeIdentityFirstFractionLift_spec, completeIdentityFirstCubicFraction_completeError_spec]
  exact sub_eq_zero.mpr (completeIdentityFirstCubicFraction_error K n h U k hC d hd z r p hp)

end FLT.Mazur.PolygonInfinitesimalStages
