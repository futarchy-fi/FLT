/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionTransport
public import FLT.Mazur.PolygonBoundaryParameterImage
public import FLT.Mazur.PolygonBoundaryStageVanishing

/-!
# Lifting global sections to the first parameter quotient

The first parameter image has the preceding stage's cohomology. Uniform
stage vanishing therefore lifts sections of the actual first parameter
quotient, including its original identification with the closed polygon.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient GlobalIdealPower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- The first parameter image inherits the preceding stage's vanishing. -/
theorem boundaryParameterImage_vanishing (m d q : ℕ)
    (hv : Subsingleton (ModuleH (tensorPower (boundaryLine K m n h) d) q)) :
    Subsingleton (ModuleH
      (multiple (stageParameterIdeal K (m + 1) n h)
        (tensorPower (boundaryLine K (m + 1) n h) d)) q) := by
  exact @moduleH_subsingleton_of_iso _ _ _ (boundaryParameterImageIso K m n h d) q
    (boundaryReduction_target_vanishing K n h m d q hv)

variable [NeZero n]

/-- The original first-parameter quotient map lifts all sections above a uniform degree. -/
theorem boundaryFirstQuotient_uniformSurjective : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Surjective
      ((projection (stageParameterIdeal K (m + 1) n h)
        (tensorPower (boundaryLine K (m + 1) n h) d) 1).app ⊤) := by
  obtain ⟨N, hN⟩ := boundaryStages_uniformVanishing K n h
  refine ⟨N, fun d hd m ↦ ?_⟩
  let I := stageParameterIdeal K (m + 1) n h
  let M := tensorPower (boundaryLine K (m + 1) n h) d
  have hv : Subsingleton (ModuleH (multiple (I ^ 1) M) 1) := by
    simpa only [pow_one] using boundaryParameterImage_vanishing K n h m d 1 (hN d hd m 0)
  exact moduleSections_surjective_of_h1 (ShortComplex.cokernelSequence (inclusion (I ^ 1) M))
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := inferInstanceAs (Mono (inclusion (I ^ 1) M)) } hv

/-- The same lift reaches the actual closed polygon via the retained quotient comparison. -/
theorem boundaryClosedSections_uniformSurjective : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Surjective
      ((SectionGradedLinePullback.powerMap (specialFiberInclusion K (m + 1) n h)
        (boundaryLineSpecialFiberIso K (m + 1) n h) d).app ⊤) := by
  obtain ⟨N, hN⟩ := boundaryFirstQuotient_uniformSurjective K n h
  refine ⟨N, fun d hd m ↦ ?_⟩
  exact moduleSections_surjective_of_comp_iso _
    (boundarySpecialQuotientIso K n h (m + 1) d) _
    (projection_boundarySpecialQuotientIso K n h (m + 1) d) (hN d hd m)

end FLT.Mazur.PolygonInfinitesimalStages
