/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphAlgebra
public import FLT.Mazur.PolygonStageFlatLayer
public import FLT.Mazur.PolygonSmoothingFlat

/-!
# Flatness detects descent of the actual first-order graph

The parameter sends the whole graph algebra into the original node algebra.
Flatness over the original first-stage coefficient ring therefore forces
both actual coordinate errors to descend. Conversely, preservation identifies
the graph with the original flat node. Flatness is a remaining geometric
condition, not an instance supplied by this construction.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentFirstStageParameter PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "C" => firstNodeBranchSubalgebra (R)
local notation "β" => firstNodeBranchPair (R)
local notation "F" => completeIdentityFirstActionBranchEquiv K n h i
local notation "D" => completeIdentityFirstActionNodeDefect K n h i
local notation "G" => completeIdentityFirstGraphAlgebra K n h i
local notation "σ" => reciprocalScale (e) (parameterUnit K)

/-- Every original function defect lies in the actual source-target graph algebra. -/
theorem completeIdentityFirstGraphAlgebra_defect (z : B) : (D) z ∈ (G) := by
  rw [completeIdentityFirstActionNodeDefect_apply]
  have hs : (C) ≤ (G) := le_sup_left
  have ht : ((F).toAlgHom.comp (β)).range ≤ (G) := le_sup_right
  exact (G).sub_mem (ht ⟨z, rfl⟩) (hs ⟨(σ) z, rfl⟩)

/-- Flatness of the actual graph forces descent of every original defect function. -/
theorem completeIdentityFirstGraphFlat_defect [Module.Flat (S) (G)] (z : B) :
    (D) z ∈ (C) := by
  let d : G := ⟨(D) z, completeIdentityFirstGraphAlgebra_defect K n h i z⟩
  have hd : (e) • d = 0 := by
    apply Subtype.ext
    exact completeIdentityFirstActionNodeDefect_parameter K n h i z
  obtain ⟨w, hw⟩ := (flat_parameter_smul_eq_zero_iff (R) 0 (G) d).mp hd
  have he : (e) • w.val = (D) z := by
    have hh := congrArg Subtype.val hw
    change (e) ^ 1 • w.val = (D) z at hh
    simpa only [pow_one] using hh
  rw [← he]
  exact completeIdentityFirstGraphAlgebra_parameter K n h i w.val w.property

/-- Coefficient-base flatness of the constructed graph suffices for full node preservation. -/
theorem completeIdentityFirstGraphFlat_preserves [Module.Flat (S) (G)]
    (p : (S)[T;T⁻¹] × (S)[T;T⁻¹]) (hp : p ∈ (C)) : (F) p ∈ (C) := by
  obtain ⟨z, hz⟩ := hp
  change (β) z = p at hz
  rw [← hz]
  have hd := completeIdentityFirstGraphFlat_defect K n h i z
  have hs : (β) ((σ) z) ∈ (C) := ⟨_, rfl⟩
  simpa only [completeIdentityFirstActionNodeDefect_apply, sub_add_cancel]
    using (C).add_mem hd hs

/-- The graph collapses to its original source exactly when the original action preserves it. -/
theorem completeIdentityFirstGraphAlgebra_eq_source_iff :
    (G) = (C) ↔ ∀ p ∈ (C), (F) p ∈ (C) := by
  change (C) ⊔ ((F).toAlgHom.comp (β)).range = (C) ↔ _
  rw [sup_eq_left]
  constructor
  · intro hg p hp
    obtain ⟨z, hz⟩ := hp
    change (β) z = p at hz
    rw [← hz]
    exact hg ⟨z, rfl⟩
  · intro hp p hz
    obtain ⟨z, hz⟩ := hz
    change (F) ((β) z) = p at hz
    rw [← hz]
    exact hp _ ⟨z, rfl⟩

/-- The exact remaining flatness question is equivalent to original node preservation. -/
theorem completeIdentityFirstGraphFlat_iff_preserves :
    Module.Flat (S) (G) ↔ ∀ p ∈ (C), (F) p ∈ (C) := by
  constructor
  · intro hf
    let _ := hf
    exact completeIdentityFirstGraphFlat_preserves K n h i
  · intro hp
    rw [(completeIdentityFirstGraphAlgebra_eq_source_iff K n h i).mpr hp]
    exact Module.Flat.of_linearEquiv (firstNodeBranchEquiv (R)).symm.toLinearEquiv

/-- Proving flatness of this unchanged finite graph proves the unchanged first positive law. -/
theorem completeIdentityFiniteLaw_one_of_graphFlat [Module.Flat (S) (G)] :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  completeIdentityFiniteLaw_one_of_branch_preservation K n h i
    (completeIdentityFirstGraphFlat_preserves K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
