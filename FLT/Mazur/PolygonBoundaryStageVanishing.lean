/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionExactness
public import FLT.Mazur.PolygonBoundaryUniformLifting

/-!
# One vanishing bound on every actual polygon stage

Serre vanishing on stage zero and on the original closed polygon gives a
single bound. The actual adjacent reduction sequences propagate this bound
through all infinitesimal stages without assuming flatness of global sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- The initial actual stage has a single bound in all positive cohomological degrees. -/
theorem boundaryStageZero_serreBound : ∃ N : ℕ, ∀ d ≥ N, ∀ q : ℕ,
    Subsingleton (ModuleH (tensorPower (boundaryLine K 0 n h) d) (q + 1)) := by
  let _ : (structureModule (family K 0 n h).left).IsFinitePresentation :=
    unitSheaf_isFinitePresentation _
  obtain ⟨N, hN⟩ := (boundaryLine_ample K 0 n h).coherent_vanishing
    (family K 0 n h).hom (structureModule (family K 0 n h).left)
  refine ⟨N, fun d hd q ↦ ?_⟩
  exact @moduleH_subsingleton_of_iso _ _ _ (ModuleSheafTensor.leftUnitor _).symm
    (q + 1) (hN d hd q)

/-- Closed direct image preserves vanishing of the actual preceding-stage tensor line. -/
theorem boundaryReduction_target_vanishing (m d q : ℕ)
    (hv : Subsingleton (ModuleH (tensorPower (boundaryLine K m n h) d) q)) :
    Subsingleton (ModuleH (boundaryReductionSequence K m n h d).X₃ q) := by
  let _ : (family K (m + 1) n h).left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (family K (m + 1) n h).hom]
    infer_instance⟩
  let _ := ((boundaryLine_rankOne K m n h).tensorPower d).isFinitePresentation
  let _ := hv
  exact (closedPushforwardModuleHEquiv (stageRestriction K m n h)
    (tensorPower (boundaryLine K m n h) d) q).toEquiv.injective.subsingleton

variable [NeZero n]

/-- Every actual stage tensor power vanishes above one bound independent of the stage. -/
theorem boundaryStages_uniformVanishing : ∃ N : ℕ, ∀ d ≥ N, ∀ m q : ℕ,
    Subsingleton (ModuleH (tensorPower (boundaryLine K m n h) d) (q + 1)) := by
  obtain ⟨N₀, h₀⟩ := boundaryStageZero_serreBound K n h
  obtain ⟨N₁, h₁⟩ := boundaryReduction_uniformVanishing K n h
  refine ⟨max N₀ N₁, fun d hd m q ↦ ?_⟩
  induction m with
  | zero => exact h₀ d (le_trans (le_max_left _ _) hd) q
  | succ m ih =>
    exact @moduleH_subsingleton_middle _ (boundaryReductionSequence K m n h d)
      (boundaryReductionSequence_shortExact K m n h d) (q + 1)
      (h₁ d (le_trans (le_max_right _ _) hd) m q)
      (boundaryReduction_target_vanishing K n h m d (q + 1) ih)

end FLT.Mazur.PolygonInfinitesimalStages
