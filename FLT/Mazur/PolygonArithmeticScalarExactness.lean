/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleSectionScalarExactness
public import FLT.Mazur.PolygonArithmeticResidueLifting

/-!
# Actual parameter-power kernels on global boundary sections

In every sufficiently positive degree, the kernel of the original adjacent
section map consists exactly of global last-parameter-power multiples.
The assertion follows from the actual closed-layer isomorphism and global
section lifting, without a flatness assumption on global sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (n : ℕ) (h : 2 ≤ n)

include hne in
/-- First-quotient lifting identifies the adjacent global kernel with actual scalar multiples. -/
theorem boundarySections_scalar_exact (m d : ℕ)
    (hp : Function.Surjective
      ((projection (stageParameterIdeal A π (m + 1) n h)
        (tensorPower (boundaryLine A π (m + 1) n h) d) 1).app ⊤)) :
    Function.Exact (fun s : Γ((boundaryReductionSequence A π m n h d).X₂, ⊤) ↦
      stageParameterSection A π (m + 1) n h ^ (m + 1) • s)
      ((boundaryReductionSequence A π m n h d).g.app ⊤) := by
  exact moduleSections_scalar_exact (boundaryReductionSequence A π m n h d)
    (boundaryReductionSequence_shortExact A π m n h d) _
    (boundaryLayerQuotientIso A π m n h hne d)
    (stageParameterSection A π (m + 1) n h ^ (m + 1))
    (projection_boundaryLayerQuotientIso A π m n h hne d) hp

variable [IsLocalRing A] [NeZero n]
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hne hgen in
/-- One degree bound identifies all actual adjacent global evaluation kernels. -/
theorem boundarySections_uniformScalarExact : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Exact (fun s : Γ((boundaryReductionSequence A π m n h d).X₂, ⊤) ↦
      stageParameterSection A π (m + 1) n h ^ (m + 1) • s)
      ((boundaryReductionSequence A π m n h d).g.app ⊤) := by
  obtain ⟨N, hN⟩ := boundaryFirstQuotient_uniformSurjective A π hne n h hgen
  exact ⟨N, fun d hd m ↦ boundarySections_scalar_exact A π hne n h m d (hN d hd m)⟩

end FLT.Mazur.PolygonArithmeticStages
