/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerComparedSections
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Canonical divisor steps under an actual section-preserving comparison

The section-preserving line square retains multiplication by the canonical
divisor section in every tensor degree.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} {I : Y.IdealSheafData} {J : X.IdealSheafData}
variable {f : X ⟶ Y} {hI : EffectiveCartier I} {hJ : EffectiveCartier J}
variable {e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}

/-- A section-preserving line square preserves the entire original pole filtration. -/
theorem DivisorLineSectionCompatible.tensorPower_cons
    (he : DivisorLineSectionCompatible f hI hJ e) (d : ℕ)
    (t : Γ(tensorPower (divisorLineBundle I hI) d, ⊤)) :
    (tensorPowerPullbackComparison f e (d + 1)).hom.app ⊤
        (pullGlobal f _ (SectionGradedMultiplication.cons _ d ⊤ (divisorSection hI ⊤) t)) =
      SectionGradedMultiplication.cons _ d ⊤ (divisorSection hJ ⊤)
        ((tensorPowerPullbackComparison f e d).hom.app ⊤ (pullGlobal f _ t)) := by
  have hs := pullGlobal_section_map f (divisorSectionMap hI) (divisorSectionMap hJ)
    e.hom he.section
  simpa only [tensorPowerComparedSection_def] using
    tensorPowerComparedSection_cons f e d (divisorSection hI ⊤) (divisorSection hJ ⊤) hs t

end FLT.Mazur.FCurve
