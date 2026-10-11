/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicModuleScalarChange
public import FLT.Mazur.AdicExtensionProjection

/-!
# Module scalar change at a specified target ideal

Equal-ideal transport makes the scalar-change comparison usable at the
original target ideal of a presentation. Its action formula uses the actual
completed projection, rather than a separately chosen scalar map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicModuleIdealTransport

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M]

/-- Equal completion ideals identify the completed module. -/
def idealEquiv {I J : Ideal S} (h : I = J) : AdicCompletion I M ≃ₗ[S]
    AdicCompletion J M := by
  subst J
  exact LinearEquiv.refl _ _

/-- Equal-ideal transport retains original elements. -/
@[simp] theorem idealEquiv_of {I J : Ideal S} (h : I = J) (m : M) :
    idealEquiv h (AdicCompletion.of I M m) = AdicCompletion.of J M m := by
  subst J
  rfl

/-- Equal-ideal transport retains completed scalar multiplication. -/
theorem idealEquiv_smul {I J : Ideal S} (h : I = J)
    (a : AdicCompletion I S) (x : AdicCompletion I M) :
    idealEquiv h (a • x) = AdicExtensionProjection.idealEquiv (R := R) h a •
      idealEquiv h x := by
  subst J
  rfl

variable [Module R M] [IsScalarTower R S M] (I : Ideal R) (J : Ideal S)
  (h : I.map (algebraMap R S) = J)

/-- Change module scalars and identify the extended ideal with the prescribed one. -/
def equiv : AdicCompletion I M ≃ₗ[R] AdicCompletion J M :=
  AdicModuleScalarChange.equiv (S := S) I ≪≫ₗ (idealEquiv h).restrictScalars R

/-- This scalar-change comparison also retains every original element. -/
@[simp] theorem equiv_of (m : M) :
    equiv I J h (AdicCompletion.of I M m) = AdicCompletion.of J M m := by
  change idealEquiv h (AdicModuleScalarChange.equiv (S := S) I
    (AdicCompletion.of I M m)) = _
  rw [AdicModuleScalarChange.equiv_of, idealEquiv_of]

/-- The prescribed comparison retains the actual completed base action. -/
theorem equiv_smul (a : AdicCompletion I R) (x : AdicCompletion I M) :
    equiv I J h (a • x) =
      AdicExtensionProjection.idealEquiv (R := R) h
        (AdicCompletionScalars.algebraMapCompletion (S := S) I a) • equiv I J h x := by
  change idealEquiv h (AdicModuleScalarChange.equiv (S := S) I (a • x)) = _
  rw [AdicModuleScalarChange.equiv_smul, idealEquiv_smul (R := R)]
  rfl

end FLT.Mazur.AdicModuleIdealTransport
