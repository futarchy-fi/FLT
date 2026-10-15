/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphGenericEquations
public import FLT.Mazur.PolygonCompleteIdentityFirstChartClosedPresentation

/-!
# Local equations of the full original first-chart closed fiber

The actual graph-plus-parameter ideal, on every compatible affine patch, is
exactly the original generic smooth-graph section kernel extended to that
patch, plus the original parameter. The order of closure and reduction is
retained, including all possible embedded components.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityActionGenericSmoothGraph
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0
local notation "g" => completeIdentityActionGenericSmoothGraph K n h
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h
local notation "t" => completeIdentityFirstAmbientParameter K n h
variable (U : (completeIdentityActionAdicChartSpace K n h 1 0 0).affineOpens)
/-- Restriction of original ambient functions to an actual affine open. -/
abbrev completeIdentityFirstAmbientRestriction : Γ((R), ⊤) ⟶ Γ((R), U) :=
  (R).presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h U

/-- Restricting the full graph-plus-parameter ideal retains the full local graph kernel. -/
theorem completeIdentityFirstChartClosedAmbientIdeal_restrict :
    (J).map (ρ).hom = (c).ker.ideal U ⊔ Ideal.span {(ρ) (t)} := by
  rw [completeIdentityFirstChartClosedAmbientIdeal, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton, completeIdentityActionGraphAdicChartRingIdeal_eq]
  exact congrArg (fun I : Ideal Γ((R), U) ↦ I ⊔ Ideal.span {(ρ) (t)})
    ((c).ker.map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top (R)⟩)
      (show U.1 ≤ ⊤ from le_top))

variable (W : (completeIdentityActionLiftSpace K n h).affineOpens)
variable (e : U.1 ≤ (completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1) ⁻¹ᵁ W.1)

/-- The full local closed-fiber ideal is computed from generic equations before reduction. -/
theorem completeIdentityFirstChartClosedAmbientIdeal_localEquations :
    (J).map (ρ).hom = (RingHom.ker ((g).app W).hom).map ((k).appLE W U e).hom ⊔
      Ideal.span {(ρ) (t)} := by
  rw [completeIdentityFirstChartClosedAmbientIdeal_restrict,
    completeIdentityActionGraphAdicChart_localGenericEquations K n h 1 0 0 W U e]

/-- Any actual generic equation is a relation in the full local original closed fiber. -/
theorem completeIdentityFirstChartClosedLocalEquation
    (z : Γ(completeIdentityActionLiftSpace K n h, W)) (hz : (g).app W z = 0) :
    ((k).appLE W U e) z ∈ (J).map (ρ).hom := by
  rw [completeIdentityFirstChartClosedAmbientIdeal_localEquations K n h U W e]
  apply Ideal.mem_sup_left
  exact Ideal.mem_map_of_mem _ hz

/-- A regular generic factor can be cancelled before forming the actual closed-fiber relation. -/
theorem completeIdentityFirstChartClosedLocalCancelledEquation
    (a z : Γ(completeIdentityActionLiftSpace K n h, W))
    (ha : IsRegular ((g).app W a)) (hz : (g).app W (a * z) = 0) :
    ((k).appLE W U e) z ∈ (J).map (ρ).hom := by
  apply completeIdentityFirstChartClosedLocalEquation K n h U W e
  apply ha.left
  simpa only [map_mul, mul_zero] using hz

/-- The exact generic-equations-plus-parameter presentation is available at every ambient point. -/
theorem completeIdentityFirstChartClosedAmbientIdeal_exists_localEquations (x : R) :
    ∃ (W : (completeIdentityActionLiftSpace K n h).affineOpens)
      (U : (R).affineOpens) (e : U.1 ≤ (k) ⁻¹ᵁ W.1), x ∈ U.1 ∧
      (J).map ((R).presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom =
        (RingHom.ker ((g).app W).hom).map ((k).appLE W U e).hom ⊔
          Ideal.span {((R).presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op) (t)} := by
  obtain ⟨W, U, e, hx, _⟩ :=
    completeIdentityActionGraphAdicChart_exists_genericEquationPatch K n h 1 0 0 x
  exact ⟨W, U, e, hx, completeIdentityFirstChartClosedAmbientIdeal_localEquations K n h U W e⟩

end FLT.Mazur.PolygonInfinitesimalStages
