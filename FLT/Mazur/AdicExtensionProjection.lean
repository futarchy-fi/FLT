/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionScalars
public import Mathlib.RingTheory.Extension.Basic

/-!
# Surjective completed presentation maps

Complete the presenting algebra at the inverse image of the target ideal.
The original surjection extends to a surjective algebra map onto the
actual completion of the target, supplying lifts of formal coordinates.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicExtensionProjection

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Equal ideals define the same completed algebra, without changing original elements. -/
def idealEquiv {I J : Ideal A} (h : I = J) :
    AdicCompletion I A ≃ₐ[R] AdicCompletion J A := by
  subst J
  exact AlgEquiv.refl

/-- Transport between equal ideals preserves the original algebra map. -/
@[simp] theorem idealEquiv_of {I J : Ideal A} (h : I = J) (a : A) :
    idealEquiv (R := R) h (AdicCompletion.of I A a) = AdicCompletion.of J A a := by
  subst J
  rfl

variable (P : Algebra.Extension R A) (I : Ideal A)

/-- The ideal defining completion of the presenting algebra. -/
def ideal : Ideal P.Ring := I.comap (algebraMap P.Ring A)

/-- Surjectivity of a presentation identifies the image of its completion ideal. -/
theorem ideal_map : (ideal P I).map (algebraMap P.Ring A) = I :=
  Ideal.map_comap_of_surjective _ P.algebraMap_surjective I

/-- Extend the presentation surjection to the completed rings. -/
def projection : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion I A :=
  (idealEquiv (R := R) (ideal_map P I)).toAlgHom.comp
    ((AdicCompletionScalars.algebraMapCompletion (S := A) (ideal P I)).restrictScalars R)

/-- On original elements, the completed projection retains the original presentation. -/
theorem projection_of (x : P.Ring) :
    projection P I (AdicCompletion.of (ideal P I) P.Ring x) =
      AdicCompletion.of I A (algebraMap P.Ring A x) := by
  change idealEquiv (R := R) (ideal_map P I)
    (AdicCompletionScalars.algebraMapCompletion (S := A) (ideal P I)
      (AdicCompletion.of (ideal P I) P.Ring x)) = _
  rw [AdicCompletionScalars.algebraMapCompletion_of, idealEquiv_of]

/-- Every element of the completed target lifts to the completed presenting algebra. -/
theorem projection_surjective : Function.Surjective (projection P I) :=
  (idealEquiv (R := R) (ideal_map P I)).surjective.comp
    (AdicCompletionScalars.algebraMapCompletion_surjective
      (S := A) (ideal P I) P.algebraMap_surjective)

end FLT.Mazur.AdicExtensionProjection
