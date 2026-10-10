/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedScalarLifting
public import FLT.Mazur.PolygonBoundaryScalarExactness

/-!
# Scalar exactness in the retained degree zero

Closed global functions lift as constants, so the original first parameter
quotient is surjective in degree zero. The adjacent kernel calculation
therefore holds in degree zero without a Serre bound.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Constants lift through the original first quotient, including its actual quotient map. -/
theorem boundaryFirstQuotient_zero_surjective (m : ℕ) :
    Function.Surjective
      ((projection (stageParameterIdeal K m n h)
        (tensorPower (boundaryLine K m n h) 0) 1).app ⊤) := by
  apply moduleSections_surjective_of_comp_iso _
    (boundarySpecialQuotientIso K n h m 0).symm _ _
    (boundaryClosedSections_zero_surjective K n h m)
  rw [← projection_boundarySpecialQuotientIso, Category.assoc,
    Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- In degree zero, the actual adjacent section kernel is the last parameter-power image. -/
theorem boundarySections_zero_scalar_exact (m : ℕ) :
    Function.Exact (fun s : Γ((boundaryReductionSequence K m n h 0).X₂, ⊤) ↦
      stageParameterSection K (m + 1) n h ^ (m + 1) • s)
      ((boundaryReductionSequence K m n h 0).g.app ⊤) :=
  boundarySections_scalar_exact K n h m 0 (boundaryFirstQuotient_zero_surjective K n h (m + 1))

/-- The same kernel identity uses the original ring map on global functions. -/
theorem stageRestriction_appTop_kernel (m : ℕ)
    (s : Γ((family K (m + 1) n h).left, ⊤)) :
    (stageRestriction K m n h).appTop s = 0 ↔
      ∃ t : Γ((family K (m + 1) n h).left, ⊤),
        stageParameterSection K (m + 1) n h ^ (m + 1) * t = s := by
  have he := boundarySections_zero_scalar_exact K n h m s
  change SectionGradedLinePullback.sectionMap (stageRestriction K m n h)
    (adjacentBoundaryLineIso K m n h) 0 ⊤ s = 0 ↔ _ at he
  rw [SectionGradedLinePullback.sectionMap_zero] at he
  exact he

end FLT.Mazur.PolygonInfinitesimalStages
