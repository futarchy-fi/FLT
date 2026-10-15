/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleSectionScalarExactness
public import FLT.Mazur.PolygonArithmeticParameterImage

/-!
# Parameter annihilators of actual global boundary sections

In every degree, the original parameter kills a global section exactly when
that section restricts to zero on the preceding stage. This uses injective
sheaf image maps, so no global section lifting or positivity is required.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient
open GlobalIdealPower IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0)
  (m n : ℕ) (h : 2 ≤ n) (d : ℕ)

include hne in
/-- Parameter annihilation is exactly vanishing on the original preceding stage. -/
theorem boundarySections_parameter_annihilator
    (s : Γ((boundaryReductionSequence A π m n h d).X₂, ⊤)) :
    stageParameterSection A π (m + 1) n h • s = 0 ↔
      (boundaryReductionSequence A π m n h d).g.app ⊤ s = 0 := by
  rw [moduleSections_scalar_zero_iff _
    ((boundaryParameterQuotientIso A π hne m n h d).hom ≫
      inclusion (stageParameterIdeal A π (m + 1) n h)
        (tensorPower (boundaryLine A π (m + 1) n h) d))
    (stageParameterSection A π (m + 1) n h)
    (projection_boundaryParameterQuotientIso A π hne m n h d) s]
  change _ ↔ (SectionGradedLinePullback.powerMap (stageRestriction A π m n h)
    (adjacentBoundaryLineIso A π m n h) d).app ⊤ s = 0
  rw [← projection_boundaryTensorQuotientIso, moduleSections_factor_zero_iff]

end FLT.Mazur.PolygonArithmeticStages
