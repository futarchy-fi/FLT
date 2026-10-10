/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionScalarExactness
public import FLT.Mazur.PolygonBoundaryClosedLifting

/-!
# Actual parameter-power kernels on global boundary sections

In every sufficiently positive degree, the kernel of the original adjacent
section map consists exactly of global last-parameter-power multiples.
The assertion follows from the actual closed-layer isomorphism and global
section lifting, without a flatness assumption on global sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- First-quotient lifting identifies the adjacent global kernel with actual scalar multiples. -/
theorem boundarySections_scalar_exact (m d : ℕ)
    (hp : Function.Surjective
      ((projection (stageParameterIdeal K (m + 1) n h)
        (tensorPower (boundaryLine K (m + 1) n h) d) 1).app ⊤)) :
    Function.Exact (fun s : Γ((boundaryReductionSequence K m n h d).X₂, ⊤) ↦
      stageParameterSection K (m + 1) n h ^ (m + 1) • s)
      ((boundaryReductionSequence K m n h d).g.app ⊤) := by
  exact moduleSections_scalar_exact (boundaryReductionSequence K m n h d)
    (boundaryReductionSequence_shortExact K m n h d) _
    (boundaryLayerQuotientIso K m n h d)
    (stageParameterSection K (m + 1) n h ^ (m + 1))
    (projection_boundaryLayerQuotientIso K m n h d) hp

variable [NeZero n]

/-- One degree bound identifies all actual adjacent global evaluation kernels. -/
theorem boundarySections_uniformScalarExact : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Exact (fun s : Γ((boundaryReductionSequence K m n h d).X₂, ⊤) ↦
      stageParameterSection K (m + 1) n h ^ (m + 1) • s)
      ((boundaryReductionSequence K m n h d).g.app ⊤) := by
  obtain ⟨N, hN⟩ := boundaryFirstQuotient_uniformSurjective K n h
  exact ⟨N, fun d hd m ↦ boundarySections_scalar_exact K n h m d (hN d hd m)⟩

end FLT.Mazur.PolygonInfinitesimalStages
