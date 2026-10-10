/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCoherentVanishing
public import FLT.Mazur.PolygonBoundaryClosedLayer
public import FLT.Mazur.PolygonInfinitesimalStageAmple
public import FLT.Mazur.PolygonInfinitesimalStageProper

/-!
# Uniform section lifting through the actual polygon stages

A single Serre bound on the original closed polygon kills the cohomology of
all adjacent reduction kernels. Thus every original adjacent section map is
surjective in every degree above that bound, uniformly in the stage index.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- One bound kills every positive cohomology group of the original closed boundary powers. -/
theorem closedBoundaryPower_serreBound : ∃ N : ℕ, ∀ d ≥ N, ∀ q : ℕ,
    Subsingleton (ModuleH (tensorPower (closedBoundaryLine K n h) d) (q + 1)) := by
  let _ := cyclicPolygon_proper K n h
  let _ : (structureModule (PolygonCyclicAtlas.scheme K n h)).IsFinitePresentation :=
    unitSheaf_isFinitePresentation _
  obtain ⟨N, hN⟩ := (specialBoundaryLine_ample K n h).coherent_vanishing
    (PolygonCyclicAtlas.toBase K n h) (structureModule (PolygonCyclicAtlas.scheme K n h))
  refine ⟨N, fun d hd q ↦ ?_⟩
  exact @moduleH_subsingleton_of_iso _ _ _ (ModuleSheafTensor.leftUnitor _).symm
    (q + 1) (hN d hd q)

/-- Closed-fiber vanishing kills the actual adjacent reduction kernel in the same degree. -/
theorem boundaryClosedLayer_vanishing (m d q : ℕ)
    (hv : Subsingleton (ModuleH (tensorPower (closedBoundaryLine K n h) d) q)) :
    Subsingleton (ModuleH (boundaryReductionSequence K m n h d).X₁ q) := by
  let _ : (family K (m + 1) n h).left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (family K (m + 1) n h).hom]
    infer_instance⟩
  let _ := ((closedBoundaryLine_rankOne K n h).tensorPower d).isFinitePresentation
  let _ := hv
  let _ := (closedPushforwardModuleHEquiv (specialFiberInclusion K (m + 1) n h)
    (tensorPower (closedBoundaryLine K n h) d) q).toEquiv.injective.subsingleton
  exact moduleH_subsingleton_of_iso (boundaryClosedLayerIso K n h m d) q

/-- The same Serre bound annihilates all original reduction kernels at all stages. -/
theorem boundaryReduction_uniformVanishing : ∃ N : ℕ, ∀ d ≥ N, ∀ m q : ℕ,
    Subsingleton (ModuleH (boundaryReductionSequence K m n h d).X₁ (q + 1)) := by
  obtain ⟨N, hN⟩ := closedBoundaryPower_serreBound K n h
  exact ⟨N, fun d hd m q ↦ boundaryClosedLayer_vanishing K n h m d (q + 1) (hN d hd q)⟩

/-- Above one degree bound every section lifts through every actual adjacent stage map. -/
theorem boundarySections_uniformSurjective : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Surjective
      (SectionGradedLinePullback.sectionMap (stageRestriction K m n h)
        (adjacentBoundaryLineIso K m n h) d ⊤) := by
  obtain ⟨N, hN⟩ := boundaryReduction_uniformVanishing K n h
  exact ⟨N, fun d hd m ↦ boundaryReduction_sections_surjective K m n h d (hN d hd m 0)⟩

end FLT.Mazur.PolygonInfinitesimalStages
