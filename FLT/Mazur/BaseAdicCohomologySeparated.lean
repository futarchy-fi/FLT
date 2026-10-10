/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicFormalInjectivity
public import FLT.Mazur.IdealAdicCohomologyRestriction
public import FLT.Mazur.ProperRingCohomologyFinite
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Separated proper cohomology for ideals in the Jacobson radical

Finite proper cohomology is adically separated by Krull intersection.
Formal injectivity then detects actual classes on the infinitesimal tower,
without completeness of the base ring.
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

/-- Original cohomology is detected by all quotients for ideals in the Jacobson radical. -/
theorem cohomologyRestriction_injective_of_le_jacobson
    (hJ : J ≤ Ideal.jacobson ⊥) (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    Function.Injective (cohomologyRestriction (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M q) := by
  let _ := Chow.source_isNoetherian f
  let _ := proper_coherent_hasFiniteRingCohomology f M q
  let _ := IsHausdorff.of_le_jacobson J (ModuleRingH (baseCohomologyScalars f) M q) hJ
  dsimp only
  rw [← formalComparison_comp_of (baseCohomologyScalars f)
    ((baseIdeal R J).comap f) M J (scalar_mem f J) q]
  exact (formalComparison_injective f J M q).comp (AdicCompletion.of_injective J _)

/-- Vanishing on every finite quotient implies actual vanishing under Krull separation. -/
theorem cohomology_subsingleton_of_quotients (hJ : J ≤ Ideal.jacobson ⊥) (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    (∀ n, Subsingleton (ModuleH (quotient ((baseIdeal R J).comap f) M n) q)) →
      Subsingleton (ModuleH M q) := by
  let _ := Chow.source_isNoetherian f
  dsimp only
  intro h
  have hi := cohomologyRestriction_injective_of_le_jacobson f J M hJ q
  refine ⟨fun x y ↦ hi ?_⟩
  apply Subtype.ext
  funext n
  exact (h n).elim _ _

end FLT.Mazur.BaseAdicCohomology
