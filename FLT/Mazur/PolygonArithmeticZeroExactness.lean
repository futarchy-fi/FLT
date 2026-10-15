/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticResidueConstants
public import FLT.Mazur.PolygonArithmeticScalarExactness

/-!
# Scalar exactness in the retained degree zero

Closed global functions lift as constants, so the original first parameter
quotient is surjective in degree zero. The adjacent kernel calculation
therefore holds in degree zero without a Serre bound.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family

variable (A : Type) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π) (n : ℕ) (h : 2 ≤ n) [NeZero n]

include hgen in
/-- Constants lift through the original first quotient, including its actual quotient map. -/
theorem boundaryFirstQuotient_zero_surjective (m : ℕ) :
    Function.Surjective
      ((projection (stageParameterIdeal A π m n h)
        (tensorPower (boundaryLine A π m n h) 0) 1).app ⊤) := by
  apply moduleSections_surjective_of_comp_iso _
    (boundaryResidueQuotientIso A π hgen (parameter_residue_zero A π hgen) n h m 0).symm _ _
    (boundaryResidueSections_zero_surjective A π (parameter_residue_zero A π hgen) n h m)
  rw [← projection_boundaryResidueQuotientIso A π hgen
    (parameter_residue_zero A π hgen) n h m 0, Category.assoc,
    Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

variable [IsNoetherianRing A] [IsDomain A] (hne : π ≠ 0)

include hne hgen in
/-- In degree zero, the actual adjacent section kernel is the last parameter-power image. -/
theorem boundarySections_zero_scalar_exact (m : ℕ) :
    Function.Exact (fun s : Γ((boundaryReductionSequence A π m n h 0).X₂, ⊤) ↦
      stageParameterSection A π (m + 1) n h ^ (m + 1) • s)
      ((boundaryReductionSequence A π m n h 0).g.app ⊤) :=
  boundarySections_scalar_exact A π hne n h m 0
    (boundaryFirstQuotient_zero_surjective A π hgen n h (m + 1))

include hne hgen in
/-- The same kernel identity uses the original ring map on global functions. -/
theorem stageRestriction_appTop_kernel (m : ℕ)
    (s : Γ((family A π (m + 1) n h).left, ⊤)) :
    (stageRestriction A π m n h).appTop s = 0 ↔
      ∃ t : Γ((family A π (m + 1) n h).left, ⊤),
        stageParameterSection A π (m + 1) n h ^ (m + 1) * t = s := by
  have he := boundarySections_zero_scalar_exact A π hgen n h hne m s
  change SectionGradedLinePullback.sectionMap (stageRestriction A π m n h)
    (adjacentBoundaryLineIso A π m n h) 0 ⊤ s = 0 ↔ _ at he
  rw [SectionGradedLinePullback.sectionMap_zero] at he
  exact he

end FLT.Mazur.PolygonArithmeticStages
