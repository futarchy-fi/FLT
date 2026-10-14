/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCanonicalLine
public import FLT.Mazur.SectionDirectImageCanonicalBasis

/-!
# The canonical integral degree-one basis

The actual canonical divisor section gives the unique degree-one basis vector.
Transport through the tensor unitor retains that section in the pole filtration.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Module
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionDirectImageMap
  SectionAdjunction.coefficient SectionAdjunction.basis SectionAdjunction.powerOneBasis

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The degree-one pole basis retains the actual canonical divisor section. -/
def completePointOneCanonicalBasis (i : Fin n) :
    Basis Unit Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 1) 0) := by
  let _ := completePointCanonicalSectionMap_isIso K n h i
  exact SectionAdjunction.powerOneBasis (exactVeroneseProjToBase K n h)
    (completePointLine K n h i) (divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤)

/-- The first-power unitor recovers exactly the original canonical divisor section. -/
theorem completePointOneCanonicalBasis_section (i : Fin n) :
    (ModuleSheafTensor.rightUnitor (completePointLine K n h i)).hom.app ⊤
      (moduleH0Equiv _ (completePointOneCanonicalBasis K n h i ())) =
        divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤ := by
  let _ := completePointCanonicalSectionMap_isIso K n h i
  exact SectionAdjunction.powerOneBasis_section (exactVeroneseProjToBase K n h)
    (completePointLine K n h i) (divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤)

end FLT.Mazur.PolygonInfinitesimalStages
