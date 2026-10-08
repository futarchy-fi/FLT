/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicCohomologyImageStability
public import FLT.Mazur.IdealAdicFormalRange

/-!
# Proper completion and compatible image quotients

The actual proper image filtration is cofinal with the base-adic filtration
in every cohomological degree. Thus formal surjectivity reduces exactly to
lifting the coordinates of compatible quotient-cohomology families.
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

/-- Proper cohomology completion identifies with compatible actual image quotients. -/
theorem completionToImages_bijective (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    Function.Bijective (completionToImages (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M J (scalar_mem f J) q) := by
  let _ := Chow.source_isNoetherian f
  apply completionToImages_bijective_of_cofinal
  obtain ⟨c, hc⟩ := imageFiltration_cohomology_le_adic f J M q
  intro n
  exact ⟨n + c, Nat.le_add_right n c, hc n⟩

/-- The proper formal image consists exactly of coordinatewise liftable families. -/
theorem mem_range_formalComparison_iff_lifts (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    ∀ y : compatibleCohomology (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q,
      y ∈ LinearMap.range (formalComparison (baseCohomologyScalars f)
        ((baseIdeal R J).comap f) M J (scalar_mem f J) q) ↔
      ∀ n, ∃ x : ModuleRingH (baseCohomologyScalars f) M q,
        moduleHMap (projection ((baseIdeal R J).comap f) M n) q x = y.val n := by
  let _ := Chow.source_isNoetherian f
  intro y
  apply mem_range_formalComparison_iff
  obtain ⟨c, hc⟩ := imageFiltration_cohomology_le_adic f J M q
  intro n
  exact ⟨n + c, Nat.le_add_right n c, hc n⟩

end FLT.Mazur.BaseAdicCohomology
