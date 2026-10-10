/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicFormalInjectivity
public import FLT.Mazur.BaseAdicFormalSurjectivity

/-!
# Proper formal functions for coherent module sheaves

The canonical comparison from completed cohomology to compatible cohomology
of the actual base-adic coefficient quotients is an isomorphism in every degree.
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

/-- The original proper formal comparison is bijective in every degree. -/
theorem formalComparison_bijective (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    Function.Bijective (formalComparison (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M J (scalar_mem f J) q) :=
  let _ := Chow.source_isNoetherian f
  ⟨formalComparison_injective f J M q, formalComparison_surjective f J M q⟩

/-- Proper formal functions, with the original canonical comparison as the forward map. -/
def formalFunctionsEquiv (q : ℕ) :
    let _ := Chow.source_isNoetherian f
    AdicCompletion J (ModuleRingH (baseCohomologyScalars f) M q) ≃ₗ[R]
      compatibleCohomology (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q :=
  let _ := Chow.source_isNoetherian f
  LinearEquiv.ofBijective
    (formalComparison (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (scalar_mem f J) q) (formalComparison_bijective f J M q)

/-- The formal-functions equivalence retains every original completion evaluation. -/
lemma formalFunctionsEquiv_apply (q : ℕ)
    (x : AdicCompletion J (ModuleRingH (baseCohomologyScalars f) M q)) :
    let _ := Chow.source_isNoetherian f
    formalFunctionsEquiv f J M q x =
      formalComparison (baseCohomologyScalars f) ((baseIdeal R J).comap f)
        M J (scalar_mem f J) q x := rfl

end FLT.Mazur.BaseAdicCohomology
