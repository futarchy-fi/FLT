/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BivariateFractionDifference
public import FLT.Mazur.PolygonCompleteIdentityFirstCubicFractions
public import FLT.Mazur.PolygonCompleteIdentityFirstFourPolynomialErrors

/-!
# Cross-multiplied actual cubic fractions with explicit node-error coefficients

On each original basic open, the actual cubic function times the scaled source
denominator differs from the scaled source numerator by explicit multiples of
dx and dy. All restrictions use that same basic open in the full adic relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing WeierstrassIntegralChart BivariateCoordinateDifference
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
local notation "S" => completeIdentityFirstFourScaledMap K
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "L" => completeIdentityFirstFourLeftCoefficient K n h
local notation "M" => completeIdentityFirstFourRightCoefficient K n h
local notation "D" => completeIdentityFirstAmbientError K n h
local notation "x" => leftCoordinate (parameter K 1)
local notation "y" => rightCoordinate (parameter K 1)
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
variable (k : Fin 3)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityCubicChartOpen K n h k)
local notation "A" => completeIdentityAdicCubicFunctions K n h 1 0 0 U k hC
variable (d : MvPolynomial (Fin 2 ⊕ Fin 2) (Ring K[T;T⁻¹] 1))
variable (hd : (completeIdentityActionAdicChartSpace K n h 1 0 0).basicOpen
  (completeIdentityFirstFourCoordinateMap K n h d) ≤
    (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1)
/-- The original global restriction to the polynomial denominator's basic open. -/
def completeIdentityFirstFractionRestriction :
    Γ((R), ⊤) →+* Γ((R), (R).basicOpen ((P) d)) :=
  ((R).presheaf.map (homOfLE le_top).op).hom

/-- Restrict the original cubic-compatible patch to this same basic open. -/
def completeIdentityFirstFractionPatchRestriction :
    Γ((R), (V).1) →+* Γ((R), (R).basicOpen ((P) d)) :=
  ((R).presheaf.map (homOfLE hd).op).hom

local notation "ρ" => completeIdentityFirstFractionRestriction K n h d
local notation "a" z => completeIdentityFirstFractionPatchRestriction K n h U d hd ((A) z)

/-- An actual cubic fraction gives the original source cross-equation with computed coefficients. -/
theorem completeIdentityFirstCubicFraction_error (z : Coordinate (E) k)
    (r : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin 2) (B))
    (hp : (a z) * (ρ) ((P) d) ^ r = (ρ) ((P) p)) :
    (a z) * (ρ) ((s) ((S) d)) ^ r - (ρ) ((s) ((S) p)) =
      ((ρ) ((L) p) - (a z) * (ρ) ((L) (d ^ r))) * (ρ) ((D) (x)) +
        ((ρ) ((M) p) - (a z) * (ρ) ((M) (d ^ r))) * (ρ) ((D) (y)) := by
  have he := fraction_error_of_differences (ρ)
    ((P) p) ((P) (d ^ r)) ((s) ((S) p)) ((s) ((S) (d ^ r)))
    ((L) p) ((L) (d ^ r)) ((M) p) ((M) (d ^ r)) ((D) (x)) ((D) (y)) (a z)
    (completeIdentityFirstFourPolynomial_error K n h p)
    (completeIdentityFirstFourPolynomial_error K n h (d ^ r))
    (by simpa only [map_pow] using hp)
  simpa only [map_pow] using he

/-- Every point has actual cubic fractions and their exact original source error equations. -/
theorem completeIdentityFirstCubicFraction_errors_cover (v : (V).1) :
    ∃ d : MvPolynomial (Fin 2 ⊕ Fin 2) (B), ∃ hd : (R).basicOpen ((P) d) ≤ (V).1,
      v.1 ∈ (R).basicOpen ((P) d) ∧ ∀ z : Coordinate (E) k,
        ∃ (r : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin 2) (B)),
          let rho := ((R).presheaf.map
            (homOfLE (show (R).basicOpen ((P) d) ≤ ⊤ from le_top)).op).hom
          let value := (R).presheaf.map (homOfLE hd).op ((A) z)
          value * rho ((P) d) ^ r = rho ((P) p) ∧
            value * rho ((s) ((S) d)) ^ r - rho ((s) ((S) p)) =
              (rho ((L) p) - value * rho ((L) (d ^ r))) * rho ((D) (x)) +
                (rho ((M) p) - value * rho ((M) (d ^ r))) * rho ((D) (y)) := by
  obtain ⟨d, hd, hv, hz⟩ := completeIdentityFirstCubicFunctions_fractions K n h U k hC v
  refine ⟨d, hd, hv, fun z ↦ ?_⟩
  obtain ⟨r, p, hp⟩ := hz z
  exact ⟨r, p, hp, completeIdentityFirstCubicFraction_error K n h U k hC d hd z r p hp⟩

end FLT.Mazur.PolygonInfinitesimalStages
