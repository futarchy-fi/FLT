/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantAffineUniversal

/-!
# Testing the full invariant scheme kernel on original coefficients

Equality after the actual invariant projection is equivalent to equality of
all original invariant coefficients. The test scheme may be nonaffine or
nonreduced; the assertion compares complete scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationInvariantSpectrum
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (a b : T ⟶ A)

/-- Normalized candidate coefficients on any test are the original invariant coefficients. -/
theorem projection_test_coefficients :
    (Scheme.ΓSpecIso (.of (compatibleFunctions p q))).inv ≫
      (a ≫ projection p q).appTop = inclusion p q ≫ a.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, projection_coefficients]

/-- The actual full scheme kernel is tested by all original invariant coefficients. -/
theorem projection_test_eq_iff :
    a ≫ projection p q = b ≫ projection p q ↔
      ∀ s : compatibleFunctions p q, a.appTop s.val = b.appTop s.val := by
  constructor
  · intro h s
    have he := congrArg (fun g ↦
      (Scheme.ΓSpecIso (.of (compatibleFunctions p q))).inv ≫ g.appTop) h
    rw [projection_test_coefficients, projection_test_coefficients] at he
    exact ConcreteCategory.congr_hom he s
  · intro h
    let _ : IsAffine (target p q) := inferInstanceAs (IsAffine (Spec _))
    apply ext_of_isAffine
    apply (cancel_epi (Scheme.ΓSpecIso (.of (compatibleFunctions p q))).inv).mp
    rw [projection_test_coefficients, projection_test_coefficients]
    ext s
    exact h s

end FLT.Mazur.SchemeRelationInvariantSpectrum
