/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePresentedSectionFractions
public import FLT.Mazur.PolygonCompleteIdentityFirstFourCoordinates
public import FLT.Mazur.PolygonCompleteIdentityAdicCubicChartMap

/-!
# Original cubic coordinates as local fractions in original node variables

The numerators and denominators belong to the polynomial presentation with
the original Laurent coefficient ring and all four original node
variables. These identities hold on the full adic relation, with nilpotents.
They do not yet compute the coefficients of the chosen numerator polynomials.
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
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "B" => Ring K[T;T⁻¹] 1
local notation "P" => completeIdentityFirstFourCoordinateMap K n h
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
variable (k : Fin 3)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityCubicChartOpen K n h k)
local notation "A" => completeIdentityAdicCubicFunctions K n h 1 0 0 U k hC

/-- Every cubic-compatible patch has node-polynomial fractions around each original point. -/
theorem completeIdentityFirstCubicFunctions_fractions (x : (V).1) :
    ∃ d : MvPolynomial (Fin 2 ⊕ Fin 2) (B), ∃ hd : (R).basicOpen ((P) d) ≤ (V).1,
      x.1 ∈ (R).basicOpen ((P) d) ∧ ∀ z : Coordinate (E) k,
        ∃ (r : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin 2) (B)),
          (R).presheaf.map (homOfLE hd).op ((A) z) *
              (R).presheaf.map (homOfLE le_top).op ((P) d) ^ r =
            (R).presheaf.map (homOfLE le_top).op ((P) p) := by
  obtain ⟨d, hd, hx, hz⟩ := AffinePresentedSectionFractions.exists_denominator (P)
    (completeIdentityFirstFourCoordinateMap_surjective K n h) (V).1 x
  exact ⟨d, hd, hx, fun z ↦ hz ((A) z)⟩

/-- The node-polynomial denominator is a unit on the entire local fraction chart. -/
theorem completeIdentityFirstCubicFunctions_denominator (d : MvPolynomial (Fin 2 ⊕ Fin 2) (B)) :
    IsUnit ((R).presheaf.map
      (homOfLE (show (R).basicOpen ((P) d) ≤ ⊤ from le_top)).op ((P) d)) :=
  AffinePresentedSectionFractions.denominator_isUnit (P) d

end FLT.Mazur.PolygonInfinitesimalStages
