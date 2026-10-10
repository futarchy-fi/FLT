/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicFormalSurjectivity
public import FLT.Mazur.IdealAdicFiniteLifting

/-!
# Actual finite-level section lifts over a Noetherian base

Proper formal functions and graded H1 vanishing lift sections to the
original proper scheme, without completing or localizing the base ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  (M : X.Modules) [M.IsFinitePresentation]

/-- Graded H1 vanishing gives surjective restriction on H0 without base completeness. -/
theorem projection_h0_surjective_of_graded_vanishing_noetherian :
    let _ := Chow.source_isNoetherian f
    (∀ k, Subsingleton (ModuleH (graded ((baseIdeal R J).comap f) M k) 1)) →
    ∀ n, Function.Surjective (moduleHMap (projection ((baseIdeal R J).comap f) M n) 0) := by
  let _ := Chow.source_isNoetherian f
  dsimp only
  intro h n
  exact projection_surjective_of_formal (baseCohomologyScalars f)
    ((baseIdeal R J).comap f) M J (scalar_mem f J) 0
    (formalComparison_surjective f J M 0)
    (fun k ↦ reduction_h0_surjective ((baseIdeal R J).comap f) M k (h k)) n

/-- The original section projection is surjective under the same graded vanishing. -/
theorem projection_sections_surjective_of_graded_vanishing_noetherian :
    let _ := Chow.source_isNoetherian f
    (∀ k, Subsingleton (ModuleH (graded ((baseIdeal R J).comap f) M k) 1)) →
    ∀ n, Function.Surjective ((projection ((baseIdeal R J).comap f) M n).app ⊤) := by
  let _ := Chow.source_isNoetherian f
  dsimp only
  intro h n s
  obtain ⟨x, hx⟩ := projection_h0_surjective_of_graded_vanishing_noetherian f J M h n
    ((moduleH0Equiv (quotient ((baseIdeal R J).comap f) M n)).symm s)
  refine ⟨moduleH0Equiv M x, ?_⟩
  rw [← moduleH0Equiv_naturality, hx]
  exact (moduleH0Equiv (quotient ((baseIdeal R J).comap f) M n)).apply_symm_apply s

end FLT.Mazur.BaseAdicCohomology
