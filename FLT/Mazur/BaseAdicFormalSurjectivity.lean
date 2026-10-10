/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicPowerKernelFinite
public import FLT.Mazur.BaseAdicImageCompletion
public import FLT.Mazur.IdealAdicConnecting
public import FLT.Mazur.PowerCohomologyKernelVanishing

/-!
# Surjectivity of the proper formal comparison

Geometric finiteness of the genuine power-cohomology kernel forces eventual
vanishing under the original transitions. Connecting-map naturality then lifts
every compatible quotient-cohomology family through the cofinal image completion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  (M : X.Modules) [M.IsFinitePresentation]

/-- Original proper power-inclusion kernels vanish under sufficiently deep transitions. -/
theorem power_kernel_eventually_zero (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    ∀ n, ∃ m, ∃ hnm : n ≤ m,
      ∀ z : ModuleRingH (baseCohomologyScalars f) (power ((baseIdeal R J).comap f) m M) q,
        moduleHMap (inclusion (((baseIdeal R J).comap f) ^ m) M) q z = 0 →
          moduleHMap (transition ((baseIdeal R J).comap f) M hnm) q z = 0 := by
  let _ := Chow.source_isNoetherian f
  exact power_kernel_eventually_zero_of_fg (baseCohomologyScalars f)
    ((baseIdeal R J).comap f) M J (scalar_mem f J) q
    (BaseAdicRees.powerCohomology_kernel_fg f J M q)

/-- The actual proper formal comparison is surjective in every cohomological degree. -/
theorem formalComparison_surjective (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    Function.Surjective (formalComparison (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M J (scalar_mem f J) q) := by
  let _ := Chow.source_isNoetherian f
  apply formalComparison_surjective_of_eventual_lifts
  · obtain ⟨c, hc⟩ := imageFiltration_cohomology_le_adic f J M q
    intro n
    exact ⟨n + c, Nat.le_add_right n c, hc n⟩
  · exact eventual_lifts_of_power_kernel_vanishing (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M q (power_kernel_eventually_zero f J M (q + 1))

end FLT.Mazur.BaseAdicCohomology
