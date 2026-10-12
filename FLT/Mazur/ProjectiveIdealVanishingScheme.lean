/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTargetVanishingIdeal
public import FLT.Mazur.FreeTargetVanishingScheme
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A closed base locus where an ideal in a projective algebra vanishes

The scheme represents killing the actual extended ideal, rather than its
support or radical. This is the affine ingredient for imposing ideal
vanishing along a finite locally free family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.ProjectiveIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Module.Projective R B]
  (J : Ideal B)

/-- The actual ideal inclusion, considered over the original coefficient ring. -/
def inclusionLinear : J →ₗ[R] B := J.subtype.restrictScalars R

/-- The coefficient ideal of all equations on the finite family. -/
def ideal : Ideal R := ProjectiveTargetVanishing.ideal (inclusionLinear R B J)

/-- The actual closed base scheme representing vanishing of the family ideal. -/
def scheme : Scheme := FreeTargetVanishing.scheme Finsupp.basisSingleOne
  ((ProjectiveTargetVanishing.embedding R B).comp (inclusionLinear R B J))

/-- The original closed immersion into the coefficient base. -/
def inclusion : scheme R B J ⟶ Spec (.of R) := FreeTargetVanishing.inclusion _ _

instance inclusion_closed : IsClosedImmersion (inclusion R B J) :=
  FreeTargetVanishing.inclusion_closed _ _

variable (A : Type) [CommRing A] [Algebra R A]

omit [Module.Projective R B] in
/-- Extending the linear inclusion is zero exactly when the extended ideal is zero. -/
theorem extendedIdeal_eq_bot_iff :
    J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = ⊥ ↔
      (inclusionLinear R B J).baseChange A = 0 := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  constructor
  · intro h
    ext x
    exact h x.property
  · intro h x hx
    exact congrArg (fun g ↦ g (1 ⊗ₜ[R] (⟨x, hx⟩ : J))) h

/-- The coefficient ideal detects actual ideal vanishing under every scalar extension. -/
theorem extendedIdeal_eq_bot_iff_coefficients :
    J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = ⊥ ↔
      ideal R B J ≤ RingHom.ker (algebraMap R A) := by
  rw [extendedIdeal_eq_bot_iff]
  exact ProjectiveTargetVanishing.baseChange_eq_zero_iff _ A

/-- Every affine test factors through the closed base locus exactly when it kills the ideal. -/
theorem factorization_iff :
    (∃ g : Spec (.of A) ⟶ scheme R B J,
      g ≫ inclusion R B J = Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
        J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = ⊥ := by
  change (∃ g : Spec (.of A) ⟶ FreeTargetVanishing.scheme _ _,
    g ≫ FreeTargetVanishing.inclusion _ _ = _) ↔ _
  rw [FreeTargetVanishing.factorization_iff,
    ProjectiveTargetVanishing.embedded_baseChange_eq_zero_iff,
    ← extendedIdeal_eq_bot_iff]

/-- The universal coefficient quotient kills the full ideal, including nilpotents. -/
theorem quotient_extendedIdeal_eq_bot :
    J.map (Algebra.TensorProduct.includeRight :
      B →ₐ[R] (R ⧸ ideal R B J) ⊗[R] B).toRingHom = ⊥ := by
  apply (extendedIdeal_eq_bot_iff R B J _).mpr
  exact ProjectiveTargetVanishing.quotient_baseChange_eq_zero _

end FLT.Mazur.ProjectiveIdealVanishing
