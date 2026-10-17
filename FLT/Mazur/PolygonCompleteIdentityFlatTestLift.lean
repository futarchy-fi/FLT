/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityLiftLocus

/-!
# Original polygon lifts on flat tests eliminate the entire exceptional graph

The test may be an actual affine completion rather than an open immersion.
A polygon-valued lift with the original cubic equation identifies the entire
graph pullback, including all possible exceptional components and nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
variable {T : Scheme} (v : T ⟶ completeIdentityActionProduct K n h 0) [Flat v]
  (F : T ⟶ exactVeroneseProj K n h)
  (hF : F ≫ completePointToIntegralCubic K n h (0 : Fin n) =
    v ≫ completeIdentityActionTarget K n h (0 : Fin n))

include hF

/-- The constructed lift controls every graph point after the actual flat test. -/
theorem completeIdentityActionFlatTestLift_graph :
    pullback.fst (p) v ≫ (l) = pullback.snd (p) v ≫ F := by
  apply completeFlat_contraction_ext K n h 0
    ((pullback.fst (p) v) ≫ (p) ≫ (s) ≫ (π))
  · rw [Category.assoc, completeIdentityActionGraphLift_structure]
  · rw [Category.assoc, completeIdentityActionLift_structure K n h v F hF,
      pullback.condition_assoc]
  · rw [Category.assoc, completeIdentityActionGraphLift_contraction,
      pullback.condition_assoc, Category.assoc, hF]

/-- A genuine lift on a flat test makes the entire original graph pullback invertible. -/
theorem completeIdentityActionFlatTestLift_graph_isIso :
    IsIso (pullback.snd (p) v) := by
  have hl := completeIdentityActionFlatTestLift_graph K n h v F hF
  let _ : Mono (pullback.snd (p) v) := by
    constructor
    intro Z f g he
    apply pullback.hom_ext
    · apply (cancel_mono (completeIdentityActionGraphInclusion K n h)).mp
      apply pullback.hom_ext
      · change (f ≫ pullback.fst (p) v) ≫ (p) = (g ≫ pullback.fst (p) v) ≫ (p)
        simp only [Category.assoc, pullback.condition]
        rw [← Category.assoc, he, Category.assoc]
      · change (f ≫ pullback.fst (p) v) ≫ (l) = (g ≫ pullback.fst (p) v) ≫ (l)
        rw [Category.assoc, hl, ← Category.assoc, he, Category.assoc, ← hl, Category.assoc]
    · exact he
  let _ : IsClosedImmersion (pullback.snd (p) v) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (Scheme.Hom.ker_eq_bot _)

end FLT.Mazur.PolygonInfinitesimalStages
