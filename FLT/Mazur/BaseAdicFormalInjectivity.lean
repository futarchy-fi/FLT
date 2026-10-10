/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicCohomologyImageStability
public import FLT.Mazur.IdealAdicFormalInjectivity

/-!
# Injectivity of the proper formal comparison in every degree

Geometric finite generation gives the reverse adic containment of the actual
image filtration. It therefore separates all completed cohomology classes.
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

/-- The actual proper formal comparison is injective in every cohomological degree. -/
theorem formalComparison_injective (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    Function.Injective (formalComparison (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M J (scalar_mem f J) q) := by
  let _ := Chow.source_isNoetherian f
  apply formalComparison_injective_of_cofinal
  obtain ⟨c, hc⟩ := imageFiltration_cohomology_le_adic f J M q
  intro n
  exact ⟨n + c, Nat.le_add_right n c, hc n⟩

end FLT.Mazur.BaseAdicCohomology
