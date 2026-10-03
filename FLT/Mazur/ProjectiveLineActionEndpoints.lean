/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPinchingDiagram
public import FLT.Mazur.ProjectiveLineUniversalAction

/-!
# Fixed endpoints in the monoidal action convention

Translate the parameter section formulas into equations on the chosen
product of the multiplicative group and the terminal point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
universe u
namespace FLT.Mazur.ProjectiveLineActionEndpoints
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type u) [Field K]
open ProjectiveLineUniversalAction
/-- The terminal point over the coefficient field. -/
abbrev point := PolygonPinching.point K
/-- The zero or infinity section of the projective line. -/
def endpointSection (b : Bool) : point K ⟶ PolygonPinching.component K :=
  if b then ProjectiveLine.infinitySection K else ProjectiveLine.zeroSection K
theorem endpoint_whisker (b : Bool) :
    (ρ_ (MultiplicativeGroupScheme.gm K)).inv.left ≫
      (MultiplicativeGroupScheme.gm K ◁ endpointSection K b).left = endpoint K b := by
  change (ρ_ (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))).inv.left ≫
    (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)) ◁
      endpointSection K b).left = _
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerLeft_left_fst (endpointSection K b)]
    exact (Over.rightUnitor_inv_left_fst
      (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))).trans
        (endpoint_fst K b).symm
  · rw [Category.assoc, Over.whiskerLeft_left_snd]
    change (ρ_ (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))).inv.left ≫
      pullback.snd _ (𝟙 _) ≫ (endpointSection K b).left = _
    simp only [Over.tensorUnit_left]
    rw [Over.rightUnitor_inv_left_snd_assoc
      (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))]
    cases b
    · exact (endpoint_snd K false).symm
    · exact (endpoint_snd K true).symm
theorem section_act (b : Bool) :
    MultiplicativeGroupScheme.gm K ◁ endpointSection K b ≫ act K =
      snd (MultiplicativeGroupScheme.gm K) (point K) ≫ endpointSection K b := by
  apply (cancel_epi (ρ_ (MultiplicativeGroupScheme.gm K)).inv).mp
  apply Over.OverMorphism.ext
  change ((ρ_ (MultiplicativeGroupScheme.gm K)).inv.left ≫
      (MultiplicativeGroupScheme.gm K ◁ endpointSection K b).left) ≫ action K = _
  rw [endpoint_whisker]
  cases b
  · rw [zero_action]
    change _ = (ρ_ (MultiplicativeGroupScheme.gm K)).inv.left ≫
      pullback.snd _ _ ≫ ProjectiveLine.zero K
    change _ =
      (ρ_ (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))).inv.left ≫
      pullback.snd _ (𝟙 _) ≫ _
    simp only [Over.tensorUnit_left]
    rw [Over.rightUnitor_inv_left_snd_assoc
      (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))]
    rfl
  · rw [infinity_action]
    change _ = (ρ_ (MultiplicativeGroupScheme.gm K)).inv.left ≫
      pullback.snd _ _ ≫ ProjectiveLine.infinity K
    change _ =
      (ρ_ (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))).inv.left ≫
      pullback.snd _ (𝟙 _) ≫ _
    simp only [Over.tensorUnit_left]
    rw [Over.rightUnitor_inv_left_snd_assoc
      (Over.mk (ProjectiveLineProductCharts.parameterToBase K (parameter K)))]
    rfl
end FLT.Mazur.ProjectiveLineActionEndpoints
