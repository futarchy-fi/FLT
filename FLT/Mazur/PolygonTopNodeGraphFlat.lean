/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphAlgebra
public import FLT.Mazur.PolygonStageFlatLayer
public import FLT.Mazur.PolygonSmoothingFlat

/-!
# Flatness and descent of the higher original branch graph

Parameter multiplication sends the whole finite graph into the source node.
Flatness then places each full top-layer defect in that same source node.
Conversely, preservation identifies the graph with the original flat node.
No flatness instance for an unverified geometric graph is supplied.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonChartScaling PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal topNodeActionDefect
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ) (a : (Ring R (m + 1))ˣ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "C" => stageNodeBranchSubalgebra R (m + 1)
local notation "β" => stageNodeBranchPair R (m + 1)
local notation "F" => stageNodeBranchSubstitution R (m + 1) u v
local notation "D" => topNodeActionDefect R m u v a
local notation "G" => topNodeGraphAlgebra R m u v
local notation "σ" => reciprocalScale (e) a

/-- Every full defect is an element of the actual source-target graph. -/
theorem topNodeGraphAlgebra_defect (z : B) : (D) z ∈ (G) := by
  rw [topNodeActionDefect_apply]
  have hs : (C) ≤ (G) := le_sup_left
  have ht : ((F).comp (β)).range ≤ (G) := le_sup_right
  exact (G).sub_mem (ht ⟨z, rfl⟩) (hs ⟨(σ) z, rfl⟩)

/-- Equality with the original node is exactly preservation by the full branch map. -/
theorem topNodeGraphAlgebra_eq_source_iff :
    (G) = (C) ↔ ∀ p ∈ (C), (F) p ∈ (C) := by
  change (C) ⊔ ((F).comp (β)).range = (C) ↔ _
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

variable
  (hu : coeffMap (restriction R m).toRingHom u.val =
    LaurentPolynomial.C (restriction R m a.val) * T 1)
  (hv : coeffMap (restriction R m).toRingHom v.val =
    LaurentPolynomial.C (restriction R m a⁻¹.val) * T 1)
include hu hv

/-- The actual top power sends every graph function into the source node algebra. -/
theorem topNodeGraphAlgebra_topParameter (z : (S)[T;T⁻¹] × (S)[T;T⁻¹]) (hz : z ∈ (G)) :
    (e) ^ (m + 1) • z ∈ (C) := by
  rw [pow_succ (e) m, mul_smul]
  exact (C).smul_mem (topNodeGraphAlgebra_parameter R m u v a hu hv z hz) ((e) ^ m)

/-- Flatness of this precise graph forces descent of every original defect. -/
theorem topNodeGraphFlat_defect [Module.Flat (S) (G)] (z : B) : (D) z ∈ (C) := by
  let d : G := ⟨(D) z, topNodeGraphAlgebra_defect R m u v a z⟩
  have hd : (e) • d = 0 := by
    apply Subtype.ext
    exact topNodeActionDefect_parameter R m u v a hu hv z
  obtain ⟨w, hw⟩ := (flat_parameter_smul_eq_zero_iff R m (G) d).mp hd
  have he : (e) ^ (m + 1) • w.val = (D) z := congrArg Subtype.val hw
  rw [← he]
  exact topNodeGraphAlgebra_topParameter R m u v a hu hv w.val w.property

/-- Original-base flatness preserves every full original node function. -/
theorem topNodeGraphFlat_preserves [Module.Flat (S) (G)]
    (p : (S)[T;T⁻¹] × (S)[T;T⁻¹]) (hp : p ∈ (C)) : (F) p ∈ (C) := by
  obtain ⟨z, hz⟩ := hp
  change (β) z = p at hz
  rw [← hz]
  have hd := topNodeGraphFlat_defect R m u v a hu hv z
  have hs : (β) ((σ) z) ∈ (C) := ⟨_, rfl⟩
  simpa only [topNodeActionDefect_apply, sub_add_cancel] using (C).add_mem hd hs

/-- Flatness is exactly the remaining node-preservation condition at each positive stage. -/
theorem topNodeGraphFlat_iff_preserves :
    Module.Flat (S) (G) ↔ ∀ p ∈ (C), (F) p ∈ (C) := by
  constructor
  · intro hf
    let _ := hf
    exact topNodeGraphFlat_preserves R m u v a hu hv
  · intro hp
    rw [(topNodeGraphAlgebra_eq_source_iff R m u v).mpr hp]
    exact Module.Flat.of_linearEquiv (stageNodeBranchEquiv R (m + 1)).symm.toLinearEquiv

end FLT.Mazur.PolygonInfinitesimalStages
