/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicLocalizedFirstCotangent
public import FLT.Mazur.AffineClosedPointAlgebra

/-!
# Original first cotangent homology at an actual affine stalk

The actual germ localizes a finite polynomial presentation of the affine
sections. Its localized conormal differential computes original stalk H1.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.AffineClosedPointQuotient

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {X : Scheme.{0}}
  (U : X.affineOpens) (x : U.1) (s : R →+* Γ(X, U)) (hs : s.FinitePresentation)

/-- The original finite polynomial presentation, localized by the actual germ. -/
def stalkConormalDifferential :
    let _ := s.toAlgebra
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
    let _ : Algebra.FinitePresentation R Γ(X, U) := hs
    let P := (Algebra.Presentation.ofFinitePresentation R Γ(X, U)).toGenerators
    (X.presheaf.stalk x ⊗[Γ(X, U)] P.toExtension.Cotangent) →ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x ⊗[Γ(X, U)] P.toExtension.CotangentSpace) := by
  let _ := s.toAlgebra
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let _ : Algebra.FinitePresentation R Γ(X, U) := hs
  let P := (Algebra.Presentation.ofFinitePresentation R Γ(X, U)).toGenerators
  exact P.toExtension.cotangentComplex.baseChange (X.presheaf.stalk x)

variable [IsNoetherianRing Γ(X, U)]

include hs in
/-- Actual original stalk first homology is finite. -/
theorem stalkH1Cotangent_finite :
    let _ := (stalkScalars U x s).toAlgebra
    Module.Finite (X.presheaf.stalk x) (Algebra.H1Cotangent R (X.presheaf.stalk x)) := by
  let _ := s.toAlgebra
  let _ := (stalkScalars U x s).toAlgebra
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let _ : IsScalarTower R Γ(X, U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ := U.2.isLocalization_stalk x
  let _ : Algebra.FinitePresentation R Γ(X, U) := hs
  exact AdicLocalizedFirstCotangent.localizedH1_finite
    (Algebra.Presentation.ofFinitePresentation R Γ(X, U)).toGenerators
    (X.presheaf.stalk x) (U.2.primeIdealOf x).asIdeal.primeCompl

variable [IsNoetherianRing (X.presheaf.stalk x)] (J : Ideal (X.presheaf.stalk x))

/-- Completion of original stalk H1 is the kernel of the completed actual germ-localized complex. -/
def stalkH1CotangentCompletionEquiv :
    let _ := s.toAlgebra
    let _ := (stalkScalars U x s).toAlgebra
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
    AdicCompletion J (Algebra.H1Cotangent R (X.presheaf.stalk x)) ≃ₗ[
      AdicCompletion J (X.presheaf.stalk x)]
        LinearMap.ker (AdicCompletion.map J (stalkConormalDifferential U x s hs)) := by
  let _ := s.toAlgebra
  let _ := (stalkScalars U x s).toAlgebra
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let _ : IsScalarTower R Γ(X, U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ := U.2.isLocalization_stalk x
  let _ : Algebra.FinitePresentation R Γ(X, U) := hs
  exact AdicLocalizedFirstCotangent.completedEquiv
    (Algebra.Presentation.ofFinitePresentation R Γ(X, U)).toGenerators
    (X.presheaf.stalk x) (U.2.primeIdealOf x).asIdeal.primeCompl J

end FLT.Mazur.AffineClosedPointQuotient
