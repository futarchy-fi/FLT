/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleSectionTransport
public import FLT.Mazur.PolygonArithmeticParameterImage
public import FLT.Mazur.PolygonArithmeticStageVanishing

/-!
# Lifting global sections to the first parameter quotient

The first parameter image has the preceding stage's cohomology. Uniform
stage vanishing therefore lifts sections of the actual first parameter
quotient, including its original identification with the closed polygon.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient GlobalIdealPower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (n : ℕ) (h : 2 ≤ n)

include hne in
/-- The first parameter image inherits the preceding stage's vanishing. -/
theorem boundaryParameterImage_vanishing (m d q : ℕ)
    (hv : Subsingleton (ModuleH (tensorPower (boundaryLine A π m n h) d) q)) :
    Subsingleton (ModuleH
      (multiple (stageParameterIdeal A π (m + 1) n h)
        (tensorPower (boundaryLine A π (m + 1) n h) d)) q) := by
  exact @moduleH_subsingleton_of_iso _ _ _ (boundaryParameterImageIso A π hne m n h d) q
    (boundaryReduction_target_vanishing A π n h m d q hv)

variable [IsLocalRing A] [NeZero n]
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hne hgen in
/-- The original first-parameter quotient map lifts all sections above a uniform degree. -/
theorem boundaryFirstQuotient_uniformSurjective : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Surjective
      ((projection (stageParameterIdeal A π (m + 1) n h)
        (tensorPower (boundaryLine A π (m + 1) n h) d) 1).app ⊤) := by
  obtain ⟨N, hN⟩ := boundaryStages_uniformVanishing A π hgen n h hne
  refine ⟨N, fun d hd m ↦ ?_⟩
  let I := stageParameterIdeal A π (m + 1) n h
  let M := tensorPower (boundaryLine A π (m + 1) n h) d
  have hv : Subsingleton (ModuleH (multiple (I ^ 1) M) 1) := by
    simpa only [pow_one] using boundaryParameterImage_vanishing A π hne n h m d 1 (hN d hd m 0)
  exact moduleSections_surjective_of_h1 (ShortComplex.cokernelSequence (inclusion (I ^ 1) M))
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := inferInstanceAs (Mono (inclusion (I ^ 1) M)) } hv

include hne hgen in
/-- The same lift reaches the actual closed polygon via the retained quotient comparison. -/
theorem boundaryResidueSections_uniformSurjective : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    Function.Surjective
      ((SectionGradedLinePullback.powerMap
        (residueFiberInclusion A π (parameter_residue_zero A π hgen) (m + 1) n h)
        (boundaryLineResidueIso A π (parameter_residue_zero A π hgen) (m + 1) n h) d).app ⊤) := by
  obtain ⟨N, hN⟩ := boundaryFirstQuotient_uniformSurjective A π hne n h hgen
  refine ⟨N, fun d hd m ↦ ?_⟩
  exact moduleSections_surjective_of_comp_iso _
    (boundaryResidueQuotientIso A π hgen (parameter_residue_zero A π hgen) n h (m + 1) d) _
    (projection_boundaryResidueQuotientIso A π hgen (parameter_residue_zero A π hgen) n h
      (m + 1) d) (hN d hd m)

end FLT.Mazur.PolygonArithmeticStages
