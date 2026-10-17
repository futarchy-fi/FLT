/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicGraphTopology
public import FLT.Mazur.PolygonCompleteIdentityAdicSectionOpen

/-!
# Coverage of all original adic graphs reduces to the special fiber

The actual compatible sections have exactly the same support at every order.
The positive-order graph projections are isomorphisms precisely when the
original special-fiber section covers the special-fiber graph.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "s" => completeIdentityAdicGraphSection K n h
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h
local notation "r" => completeIdentityAdicGraphRestriction K n h
local notation "d" => completeIdentityFiniteRestriction K n h

/-- The full original input transition covers every point of the next thickening. -/
instance completeIdentityFiniteRestriction_surjective (m : ℕ) : Surjective (d m) := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := (r m).surjective (s (m + 1) y)
  refine ⟨p m x, ?_⟩
  have he := congrArg (p (m + 1)) hx
  change (r m ≫ p (m + 1)) x = (s (m + 1) ≫ p (m + 1)) y at he
  rw [completeIdentityAdicGraphRestriction_source,
    completeIdentityAdicGraphSection_projection] at he
  exact he

/-- The whole section image pulls back exactly under the original graph restriction. -/
theorem completeIdentityAdicGraphRestriction_mem_section (m : ℕ)
    (x : completeIdentityActionGraphStage K n h m) :
    r m x ∈ Set.range (s (m + 1)) ↔ x ∈ Set.range (s m) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (d m).surjective y
    refine ⟨z, (r m).isClosedEmbedding.injective ?_⟩
    change (s m ≫ r m) z = r m x
    rw [← completeIdentityAdicGraphSection_restriction]
    exact hy
  · rintro ⟨y, rfl⟩
    refine ⟨d m y, ?_⟩
    exact congrArg (fun f ↦ f y) (completeIdentityAdicGraphSection_restriction K n h m)

/-- Adjacent section images cover their entire graphs simultaneously. -/
theorem completeIdentityAdicGraphSection_surjective_succ_iff (m : ℕ) :
    Surjective (s (m + 1)) ↔ Surjective (s m) := by
  constructor
  · intro hs
    let _ := hs
    constructor
    intro x
    exact (completeIdentityAdicGraphRestriction_mem_section K n h m x).mp
      ((s (m + 1)).surjective (r m x))
  · intro hs
    let _ := hs
    constructor
    intro y
    obtain ⟨x, rfl⟩ := (r m).surjective y
    exact (completeIdentityAdicGraphRestriction_mem_section K n h m x).mpr ((s m).surjective x)

/-- Coverage at any finite order is exactly coverage of the actual original special fiber. -/
theorem completeIdentityAdicGraphSection_surjective_iff_zero (m : ℕ) :
    Surjective (s m) ↔ Surjective (s 0) := by
  induction m with
  | zero => rfl
  | succ m ih => exact (completeIdentityAdicGraphSection_surjective_succ_iff K n h m).trans ih

/-- Every positive-order projection is invertible exactly when the special section covers. -/
theorem completeIdentityAdicGraphProjection_isIso_iff_zero (m : ℕ) :
    IsIso (p (m + 1)) ↔ Surjective (s 0) := by
  rw [← completeIdentityAdicGraphSection_surjective_iff_zero K n h (m + 1)]
  have hc : IsIso (s (m + 1) ≫ p (m + 1)) := by
    rw [completeIdentityAdicGraphSection_projection]
    infer_instance
  constructor
  · intro hp
    let _ := hp
    let _ := IsIso.of_isIso_comp_right (s (m + 1)) (p (m + 1))
    infer_instance
  · intro hs
    let _ := (isIso_iff_isOpenImmersion_and_surjective (s (m + 1))).mpr
      ⟨completeIdentityAdicGraphSection_open K n h m, hs⟩
    exact IsIso.of_isIso_comp_left (s (m + 1)) (p (m + 1))

end FLT.Mazur.PolygonInfinitesimalStages
