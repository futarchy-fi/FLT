/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantSpectrum
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Dominance of the full invariant candidate

The candidate projection is injective on global functions because its normalized
coefficient map is the inclusion of the actual invariant subring. A quasi-compact
source therefore has dense image. This does not assert surjectivity or flatness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A)

/-- The full invariant candidate projection loses no global coefficient. -/
theorem projection_appTop_injective : Function.Injective (projection p q).appTop := by
  have h : Function.Injective
      ((Scheme.ΓSpecIso (.of (SchemeEffectiveEpiSections.compatibleFunctions p q))).inv ≫
        (projection p q).appTop) := by
    rw [projection_coefficients]
    exact Subtype.val_injective
  change Function.Injective ((projection p q).appTop ∘
    (Scheme.ΓSpecIso (.of (SchemeEffectiveEpiSections.compatibleFunctions p q))).inv) at h
  exact h.of_comp_right
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (SchemeEffectiveEpiSections.compatibleFunctions p q))).inv).2

/-- Quasi-compact original sources have dense image in their full invariant candidate. -/
instance projection_isDominant [CompactSpace A] : IsDominant (projection p q) := by
  let _ : IsAffine (target p q) := inferInstanceAs (IsAffine (Spec _))
  exact isDominant_of_of_appTop_injective (projection_appTop_injective p q)

end FLT.Mazur.SchemeRelationInvariantSpectrum
