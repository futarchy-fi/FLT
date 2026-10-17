/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicSectionReduction

/-!
# The full original sections are Cartesian through every adic transition

The section at order zero is an open immersion as well. The original special
fiber therefore already contains the same clopen section and coverage obstruction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "s" => completeIdentityAdicGraphSection K n h
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h
local notation "r" => completeIdentityAdicGraphRestriction K n h m
local notation "d" => completeIdentityFiniteRestriction K n h m

/-- The entire original section commutes with adjacent base change as a Cartesian square. -/
theorem completeIdentityAdicGraphSection_isPullback :
    IsPullback (d) (s m) (s (m + 1)) (r) := by
  have hf (c : PullbackCone (s (m + 1)) (r)) : c.snd ≫ p m ≫ (d) = c.fst := by
    have he := congrArg (fun f ↦ f ≫ p (m + 1)) c.condition
    simpa only [Category.assoc, completeIdentityAdicGraphSection_projection,
      Category.comp_id, completeIdentityAdicGraphRestriction_source] using he.symm
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (completeIdentityAdicGraphSection_restriction K n h m)
    (fun c ↦ c.snd ≫ p m) ?_ ?_ ?_)
  · intro c
    exact (Category.assoc _ _ _).trans (hf c)
  · intro c
    apply (cancel_mono (r)).mp
    calc
      ((c.snd ≫ p m) ≫ s m) ≫ (r) = (c.snd ≫ p m ≫ (d)) ≫ s (m + 1) := by
        simp only [Category.assoc, completeIdentityAdicGraphSection_restriction]
      _ = c.fst ≫ s (m + 1) := by rw [hf c]
      _ = c.snd ≫ (r) := c.condition
  · intro c k _ hk
    have he := congrArg (fun f ↦ f ≫ p m) hk
    simpa only [Category.assoc, completeIdentityAdicGraphSection_projection,
      Category.comp_id] using he

/-- Every original adic section is open, including the actual special-fiber section. -/
theorem completeIdentityAdicGraphSection_open_all : IsOpenImmersion (s m) := by
  let _ := completeIdentityAdicGraphSection_open K n h m
  exact MorphismProperty.of_isPullback
    (completeIdentityAdicGraphSection_isPullback K n h m) inferInstance

/-- At every order, graph inversion is equivalent to coverage of the unchanged special fiber. -/
theorem completeIdentityAdicGraphProjection_isIso_iff_special :
    IsIso (p m) ↔ Surjective (s 0) := by
  rw [← completeIdentityAdicGraphSection_surjective_iff_zero K n h m]
  have hc : IsIso (s m ≫ p m) := by
    rw [completeIdentityAdicGraphSection_projection]
    infer_instance
  constructor
  · intro hp
    let _ := hp
    let _ := IsIso.of_isIso_comp_right (s m) (p m)
    infer_instance
  · intro hs
    let _ := (isIso_iff_isOpenImmersion_and_surjective (s m)).mpr
      ⟨completeIdentityAdicGraphSection_open_all K n h m, hs⟩
    exact IsIso.of_isIso_comp_left (s m) (p m)

end FLT.Mazur.PolygonInfinitesimalStages
