/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AmpleCoherentVanishing
public import FLT.Mazur.PolygonArithmeticBoundaryAmple
public import FLT.Mazur.PolygonArithmeticClosedLayer
public import FLT.Mazur.PolygonArithmeticStageProper
public import FLT.Mazur.PolygonBoundaryUniformLifting

/-!
# Uniform section lifting through the actual polygon stages

A single Serre bound on the original closed polygon kills the cohomology of
all adjacent reduction kernels. Thus every original adjacent section map is
surjective in every degree above that bound, uniformly in the stage index.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsDomain A] (π : A) (hne : π ≠ 0)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π) (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "K" => IsLocalRing.ResidueField A
open PolygonInfinitesimalStages (closedBoundaryLine closedBoundaryLine_rankOne
  closedBoundaryPower_serreBound)

include hne hgen in
/-- Closed-fiber vanishing kills the actual adjacent reduction kernel in the same degree. -/
theorem boundaryClosedLayer_vanishing (m d q : ℕ)
    (hv : Subsingleton (ModuleH (tensorPower (closedBoundaryLine K n h) d) q)) :
    Subsingleton (ModuleH (boundaryReductionSequence A π m n h d).X₁ q) := by
  let _ : (family A π (m + 1) n h).left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (family A π (m + 1) n h).hom]
    infer_instance⟩
  let _ := ((closedBoundaryLine_rankOne K n h).tensorPower d).isFinitePresentation
  let _ := hv
  let _ := (closedPushforwardModuleHEquiv
    (residueFiberInclusion A π (parameter_residue_zero A π hgen) (m + 1) n h)
    (tensorPower (closedBoundaryLine K n h) d) q).toEquiv.injective.subsingleton
  exact moduleH_subsingleton_of_iso (boundaryClosedLayerIso A π hne hgen
    (parameter_residue_zero A π hgen) n h m d) q

include hne hgen in
/-- The same Serre bound annihilates all original reduction kernels at all stages. -/
theorem boundaryReduction_uniformVanishing : ∃ N : ℕ, ∀ d ≥ N, ∀ m q : ℕ,
    Subsingleton (ModuleH (boundaryReductionSequence A π m n h d).X₁ (q + 1)) := by
  obtain ⟨N, hN⟩ := closedBoundaryPower_serreBound K n h
  exact ⟨N, fun d hd m q ↦
    boundaryClosedLayer_vanishing A π hne hgen n h m d (q + 1) (hN d hd q)⟩

include hne hgen in
/-- Above one degree bound every section lifts through every actual adjacent stage map. -/
theorem boundarySections_uniformSurjective : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Surjective
      (SectionGradedLinePullback.sectionMap (stageRestriction A π m n h)
        (adjacentBoundaryLineIso A π m n h) d ⊤) := by
  obtain ⟨N, hN⟩ := boundaryReduction_uniformVanishing A π hne hgen n h
  exact ⟨N, fun d hd m ↦ boundaryReduction_sections_surjective A π m n h d (hN d hd m 0)⟩

end FLT.Mazur.PolygonArithmeticStages
