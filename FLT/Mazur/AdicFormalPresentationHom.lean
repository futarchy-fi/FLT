/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicPolynomialPresentationLift
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Actual extension morphisms over a formal algebra comparison

The surjective completed presentation is an extension of the completed
algebra. Constructed polynomial lifts define genuine extension morphisms,
and hence maps of conormal modules and their original cotangent complexes.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFormalPresentationHom

open AdicExtensionProjection AdicPolynomialPresentationLift

variable {R A B ι : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The surjective completed presentation, as an actual algebra extension. -/
def completed (Q : Algebra.Extension R B) (J : Ideal B) :
    Algebra.Extension R (AdicCompletion J B) :=
  Algebra.Extension.ofSurjective (projection Q J) (projection_surjective Q J)

/-- The source algebra acts through its original completion and the given formal map. -/
def sourceScalars (I : Ideal A) (J : Ideal B)
    (e : AdicCompletion I A →ₐ[R] AdicCompletion J B) : A →ₐ[R] AdicCompletion J B :=
  e.comp (IsScalarTower.toAlgHom R A (AdicCompletion I A))

variable (P : Algebra.Generators R A ι) (Q : Algebra.Extension R B)
  (I : Ideal A) (J : Ideal B) (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)

/-- The chosen formal polynomial lift is a genuine map of extensions over its actual scalar map. -/
def hom :
    let _ := (sourceScalars I J e).toAlgebra
    P.toExtension.Hom (completed Q J) := by
  let _ := (sourceScalars I J e).toAlgebra
  exact
    { toRingHom := (lift P Q I J e).toRingHom
      toRingHom_algebraMap := (lift P Q I J e).commutes
      algebraMap_toRingHom := projection_lift P Q I J e }

/-- The map of conormal modules induced by the constructed formal polynomial lift. -/
def conormalMap :
    let _ := (sourceScalars I J e).toAlgebra
    P.toExtension.Cotangent →ₗ[A] (completed Q J).Cotangent := by
  let _ := (sourceScalars I J e).toAlgebra
  exact Algebra.Extension.Cotangent.map (hom P Q I J e)

/-- The degree-zero map induced by the same formal polynomial lift. -/
def spaceMap :
    let _ := (sourceScalars I J e).toAlgebra
    P.toExtension.CotangentSpace →ₗ[A] (completed Q J).CotangentSpace := by
  let _ := (sourceScalars I J e).toAlgebra
  exact Algebra.Extension.CotangentSpace.map (hom P Q I J e)

/-- These maps commute with the genuine conormal differentials before further completion. -/
theorem chainMap :
    let _ := (sourceScalars I J e).toAlgebra
    ∀ x : P.toExtension.Cotangent,
      spaceMap P Q I J e (P.toExtension.cotangentComplex x) =
        (completed Q J).cotangentComplex (conormalMap P Q I J e x) := by
  let _ := (sourceScalars I J e).toAlgebra
  exact Algebra.Extension.CotangentSpace.map_cotangentComplex (hom P Q I J e)

end FLT.Mazur.AdicFormalPresentationHom
