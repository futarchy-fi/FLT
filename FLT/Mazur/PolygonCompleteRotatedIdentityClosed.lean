/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteRotatedIdentityOpen
public import FLT.Mazur.PolygonCompleteClosedActionRotation

/-!
# The exact closed fiber of each rotated identity chart

The original complete rotation carries each full Laurent normalization
component to the component with the translated label. Consequently every
rotated identity chart has precisely that torus as its closed fiber.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonCyclicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase completeRotation
  completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "j" => completeClosedFiberInclusion K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "t" k => Over.Hom.left (torusToComponent K ≫ componentι K n k ≫ p)

/-- Whole-family rotation retains the original coordinate on each closed Laurent component. -/
@[reassoc] theorem completeClosedTorus_rotation (a : ZMod n) (i : Fin n) :
    (t i) ≫ (j) ≫ completeRotation K n h a = (t (rotateIndex a i)) ≫ (j) := by
  rw [← closedRotation_completeClosedFiberInclusion]
  have H := componentMap_completeCartesianRotation_closed K n h a i
  rw [completeCartesianRotation_closed] at H
  simp only [componentι_normalization, Over.comp_left, Over.homMk_left]
  simp only [Category.assoc, reassoc_of% H]

/-- The closed inverse image of a translated identity chart is exactly its translated torus. -/
theorem completeRotatedIdentityOpen_closed_preimage (i : Fin n) (a : ZMod n) :
    let _ := torus_isOpenImmersion K n (by omega) p q hp (rotateIndex a i)
    (j) ⁻¹ᵁ completeRotatedIdentityOpen K n h i a =
      (t (rotateIndex a i)).opensRange := by
  let _ := torus_isOpenImmersion K n (by omega) p q hp i
  let _ := torus_isOpenImmersion K n (by omega) p q hp (rotateIndex a i)
  apply TopologicalSpace.Opens.ext
  ext x
  change completeRotation K n h (-a) ((j) x) ∈ completePointIdentityOpen K n h i ↔ _
  have Hx := congrArg (fun v ↦ v x)
    (closedRotation_completeClosedFiberInclusion K n h (-a))
  change (j) (closedRotation K n h (-a) x) =
    completeRotation K n h (-a) ((j) x) at Hx
  rw [← Hx]
  change closedRotation K n h (-a) x ∈
    (j) ⁻¹ᵁ completePointIdentityOpen K n h i ↔ _
  rw [completePointIdentityOpen_closed_preimage]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, (j).isClosedEmbedding.injective ?_⟩
    have he := congrArg (fun y ↦ completeRotation K n h a ((j) y)) hz
    have hr := congrArg (fun v ↦ v z) (completeClosedTorus_rotation K n h a i)
    have hc := congrArg (fun v ↦ v ((j) x)) (completeRotation_add K n h (-a) a)
    rw [neg_add_cancel, completeRotation_zero] at hc
    exact hr.symm.trans (he.trans ((congrArg (completeRotation K n h a) Hx).trans hc.symm))
  · rintro ⟨z, rfl⟩
    refine ⟨z, (j).isClosedEmbedding.injective ?_⟩
    have he := completeClosedTorus_rotation K n h (-a) (rotateIndex a i)
    rw [← rotateIndex_add, add_neg_cancel, rotateIndex_zero] at he
    have hz := congrArg (fun v ↦ v z) he
    have hc := congrArg (fun v ↦ v ((t (rotateIndex a i)) z))
      (closedRotation_completeClosedFiberInclusion K n h (-a))
    exact hz.symm.trans hc.symm

end FLT.Mazur.PolygonInfinitesimalStages
