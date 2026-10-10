/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionScalarExactness
public import FLT.Mazur.PolygonBoundaryParameterImage

/-!
# Parameter annihilators of actual global boundary sections

In every degree, the original parameter kills a global section exactly when
that section restricts to zero on the preceding stage. This uses injective
sheaf image maps, so no global section lifting or positivity is required.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient
open GlobalIdealPower IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] [IsNoetherianRing R]
  (m n : ℕ) (h : 2 ≤ n) (d : ℕ)

/-- Parameter annihilation is exactly vanishing on the original preceding stage. -/
theorem boundarySections_parameter_annihilator
    (s : Γ((boundaryReductionSequence R m n h d).X₂, ⊤)) :
    stageParameterSection R (m + 1) n h • s = 0 ↔
      (boundaryReductionSequence R m n h d).g.app ⊤ s = 0 := by
  rw [moduleSections_scalar_zero_iff _
    ((boundaryParameterQuotientIso R m n h d).hom ≫
      inclusion (stageParameterIdeal R (m + 1) n h)
        (tensorPower (boundaryLine R (m + 1) n h) d))
    (stageParameterSection R (m + 1) n h)
    (projection_boundaryParameterQuotientIso R m n h d) s]
  change _ ↔ (SectionGradedLinePullback.powerMap (stageRestriction R m n h)
    (adjacentBoundaryLineIso R m n h) d).app ⊤ s = 0
  rw [← projection_boundaryTensorQuotientIso, moduleSections_factor_zero_iff]

end FLT.Mazur.PolygonInfinitesimalStages
