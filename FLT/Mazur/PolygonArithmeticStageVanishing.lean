/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleSectionExactness
public import FLT.Mazur.PolygonArithmeticUniformLifting

/-!
# One vanishing bound on every actual polygon stage

Serre vanishing on stage zero and on the original closed polygon gives a
single bound. The actual adjacent reduction sequences propagate this bound
through all arithmetic stages without assuming flatness of global sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  (π : A) (hgen : IsLocalRing.maximalIdeal A = ideal A π) (n : ℕ) (h : 2 ≤ n)

include hgen in
/-- The initial actual stage has a single bound in all positive cohomological degrees. -/
theorem boundaryStageZero_serreBound : ∃ N : ℕ, ∀ d ≥ N, ∀ q : ℕ,
    Subsingleton (ModuleH (tensorPower (boundaryLine A π 0 n h) d) (q + 1)) := by
  let _ := family_proper A π hgen 0 n h
  let _ : (structureModule (family A π 0 n h).left).IsFinitePresentation :=
    unitSheaf_isFinitePresentation _
  obtain ⟨N, hN⟩ := (boundaryLine_ample A π hgen 0 n h).coherent_vanishing
    (family A π 0 n h).hom (structureModule (family A π 0 n h).left)
  refine ⟨N, fun d hd q ↦ ?_⟩
  exact @moduleH_subsingleton_of_iso _ _ _ (ModuleSheafTensor.leftUnitor _).symm
    (q + 1) (hN d hd q)

omit [IsLocalRing A] in
/-- Closed direct image preserves vanishing of the actual preceding-stage tensor line. -/
theorem boundaryReduction_target_vanishing (m d q : ℕ)
    (hv : Subsingleton (ModuleH (tensorPower (boundaryLine A π m n h) d) q)) :
    Subsingleton (ModuleH (boundaryReductionSequence A π m n h d).X₃ q) := by
  let _ : (family A π (m + 1) n h).left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (family A π (m + 1) n h).hom]
    infer_instance⟩
  let _ := ((boundaryLine_rankOne A π m n h).tensorPower d).isFinitePresentation
  let _ := hv
  exact (closedPushforwardModuleHEquiv (stageRestriction A π m n h)
    (tensorPower (boundaryLine A π m n h) d) q).toEquiv.injective.subsingleton

variable [NeZero n] [IsDomain A] (hne : π ≠ 0)

include hgen hne in
/-- Every actual stage tensor power vanishes above one bound independent of the stage. -/
theorem boundaryStages_uniformVanishing : ∃ N : ℕ, ∀ d ≥ N, ∀ m q : ℕ,
    Subsingleton (ModuleH (tensorPower (boundaryLine A π m n h) d) (q + 1)) := by
  obtain ⟨N₀, h₀⟩ := boundaryStageZero_serreBound A π hgen n h
  obtain ⟨N₁, h₁⟩ := boundaryReduction_uniformVanishing A π hne hgen n h
  refine ⟨max N₀ N₁, fun d hd m q ↦ ?_⟩
  induction m with
  | zero => exact h₀ d (le_trans (le_max_left _ _) hd) q
  | succ m ih =>
    exact @moduleH_subsingleton_middle _ (boundaryReductionSequence A π m n h d)
      (boundaryReductionSequence_shortExact A π m n h d) (q + 1)
      (h₁ d (le_trans (le_max_right _ _) hd) m q)
      (boundaryReduction_target_vanishing A π n h m d (q + 1) ih)

end FLT.Mazur.PolygonArithmeticStages
