/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicFormalFunctions
public import FLT.Mazur.FiniteModuleAdicCompleteLarge
public import FLT.Mazur.IdealAdicCohomologyRestriction
public import FLT.Mazur.ProperRingCohomologyFinite

/-!
# Reconstructing proper cohomology over a complete Noetherian base

Finite proper cohomology is complete because the base ring is complete.
Formal functions therefore reconstructs actual, unique cohomology classes
from compatible classes on the original infinitesimal quotients.
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
  [IsAdicComplete J R] (M : X.Modules) [M.IsFinitePresentation]

omit [X.IsSeparated] in
/-- Proper coherent cohomology is complete; no completeness hypothesis on it is needed. -/
theorem cohomology_isAdicComplete (q : ℕ) :
    IsAdicComplete J (ModuleRingH (baseCohomologyScalars f) M q) := by
  let _ := proper_coherent_hasFiniteRingCohomology f M q
  exact FiniteModuleAdicComplete.isAdicComplete_large J
    (ModuleRingH (baseCohomologyScalars f) M q)

/-- Restriction from actual proper cohomology to its infinitesimal tower is bijective. -/
theorem cohomologyRestriction_bijective (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    Function.Bijective (cohomologyRestriction (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M q) := by
  let _ := Chow.source_isNoetherian f
  let _ := cohomology_isAdicComplete f J M q
  dsimp only
  rw [← formalComparison_comp_of (baseCohomologyScalars f)
    ((baseIdeal R J).comap f) M J (scalar_mem f J) q]
  exact (formalComparison_bijective f J M q).comp (AdicCompletion.of_bijective J _)

/-- The original restriction map is a linear equivalence over a complete base. -/
def cohomologyRestrictionEquiv (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    ModuleRingH (baseCohomologyScalars f) M q ≃ₗ[R]
      compatibleCohomology (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q :=
  let _ := Chow.source_isNoetherian f
  LinearEquiv.ofBijective
    (cohomologyRestriction (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q)
    (cohomologyRestriction_bijective f J M q)

/-- The equivalence evaluates by the original coefficient projection. -/
lemma cohomologyRestrictionEquiv_eval (q n : ℕ)
    (x : ModuleRingH (baseCohomologyScalars f) M q) :
    let _ := Chow.source_isNoetherian f
    (cohomologyRestrictionEquiv f J M q x).val n =
      moduleHMap (projection ((baseIdeal R J).comap f) M n) q x := rfl

/-- Every compatible infinitesimal family comes from exactly one actual cohomology class. -/
theorem existsUnique_cohomologyClass (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    ∀ x : compatibleCohomology (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q,
      ∃! y : ModuleRingH (baseCohomologyScalars f) M q,
        ∀ n, moduleHMap (projection ((baseIdeal R J).comap f) M n) q y = x.val n := by
  let _ := Chow.source_isNoetherian f
  exact existsUnique_class_of_bijective (baseCohomologyScalars f)
    ((baseIdeal R J).comap f) M q (cohomologyRestriction_bijective f J M q)

end FLT.Mazur.BaseAdicCohomology
