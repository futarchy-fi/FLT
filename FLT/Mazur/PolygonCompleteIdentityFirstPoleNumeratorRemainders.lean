/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstFractionLifts
public import FLT.Mazur.PolygonCompleteIdentityCubicDenominators

/-!
# Original pole sections constrain the actual local cubic numerator

The cross-multiplied polynomial numerator represents the retained normalized
pole section in the original pulled-back line, modulo the exact parameter-square
remainder. This retains the chosen sections rather than replacing them by an
abstract cubic triple. Their particular node-polynomial coefficients remain to
be calculated from this section equation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  ModuleSheafTensor.tensor
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "B" => Ring K[T;T⁻¹] 1
local notation "P" => completeIdentityFirstFourCoordinateMap K n h
local notation "L" => completeIdentityAdicAmbientLift K n h 1 0 0 U
local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "M" => tensorPower (completePointLine K n h (0 : Fin n)) 3
local notation "T" => completePointProjectiveSections K n h (0 : Fin n)
local notation "q" => pullback.snd (completeIdentityActionTarget K n h 0)
  (completePointToIntegralCubic K n h 0)
local notation "N" => Functor.obj (Scheme.Modules.pullback (q)) (M)

/-- The original normalized pole section in the pulled-back complete patch line. -/
def completeIdentityFirstPolePatchSection (j : Fin 3) : Γ((N), (W).1) :=
  (N).presheaf.map (homOfLE (show (W).1 ≤ ⊤ from le_top)).op
    (pullGlobal (q) (M) (T j))
local notation "s" j => completeIdentityFirstPolePatchSection K n h U j
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

/-- A cubic numerator represents the original pole section with a parameter-square error. -/
theorem completeIdentityFirstCubicFraction_pole_remainder
    (hU : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
      completeIdentityAdicNodeNeighborhood K n h 1 0 0)
    (j : Fin 3) (r : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin 2) (B))
    (hp : (res) ((A) (coord (E) k j)) * (ρ) ((P) d) ^ r = (ρ) ((P) p)) :
    ∃ (v : ℕ) (w : Γ((N), (W).1)),
      (L) ((P) d) ^ v • ((L) ((P) d) ^ r • (s j) - (L) ((P) p) • (s k)) =
        (τ) ^ 2 • w := by
  have hs : (F) (coord (E) k j) • (s k) = (s j) := by
    rw [completeIdentityCubicPatchFunctions_ratio]
    exact sectionRatioOn_smul _ _ _ _ _
  obtain ⟨v, c, hc⟩ := completeIdentityFirstCubicFraction_remainder
    K n h U d hd hU k hC (coord (E) k j) r p hp
  refine ⟨v, c • (s k), ?_⟩
  calc
    _ = ((L) ((P) d) ^ v *
        ((F) (coord (E) k j) * (L) ((P) d) ^ r - (L) ((P) p))) • (s k) := by
      rw [← hs]
      simp only [smul_sub, smul_smul]
      rw [← sub_smul]
      congr 1
      ring
    _ = _ := by rw [hc, mul_smul]

end FLT.Mazur.PolygonInfinitesimalStages
