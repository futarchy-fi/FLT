/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeTargetVanishingIdeal
public import Mathlib.Algebra.Module.Projective

/-!
# Vanishing equations with a projective target

A projective target embeds as a direct summand of a free module. Applying
the free-target equations to this split embedding gives a coefficient ideal
which detects vanishing after every scalar extension. No flatness of the
test algebra or finite generation of the source is required.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.ProjectiveTargetVanishing
variable (R N : Type*) [CommRing R] [AddCommGroup N] [Module R N] [Module.Projective R N]

/-- A splitting supplied by the target's projectivity. -/
def embedding : N →ₗ[R] N →₀ R := (Module.Projective.out (R := R) (P := N)).choose

/-- The canonical free-module retraction splits the chosen embedding. -/
theorem retraction_embedding :
    (Finsupp.linearCombination R id).comp (embedding R N) = LinearMap.id := by
  ext x
  exact (Module.Projective.out (R := R) (P := N)).choose_spec x

variable {R N} {M : Type*} [AddCommGroup M] [Module R M] (f : M →ₗ[R] N)

/-- The coefficients of the map in a split free target. -/
def ideal : Ideal R :=
  FreeTargetVanishing.ideal (Finsupp.basisSingleOne : Module.Basis N R (N →₀ R))
    ((embedding R N).comp f)

variable (A : Type*) [CommRing A] [Algebra R A]

/-- The split embedding detects zero maps after arbitrary, possibly nonflat base change. -/
theorem embedded_baseChange_eq_zero_iff :
    ((embedding R N).comp f).baseChange A = 0 ↔ f.baseChange A = 0 := by
  rw [LinearMap.baseChange_comp]
  constructor
  · intro h
    have hs : (Finsupp.linearCombination R id).baseChange A ∘ₗ
        (embedding R N).baseChange A = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, retraction_embedding, LinearMap.baseChange_id]
    calc
      f.baseChange A = LinearMap.id.comp (f.baseChange A) := (LinearMap.id_comp _).symm
      _ = (Finsupp.linearCombination R id).baseChange A ∘ₗ
          ((embedding R N).baseChange A ∘ₗ f.baseChange A) := by
        rw [← LinearMap.comp_assoc, hs]
      _ = 0 := by rw [h, LinearMap.comp_zero]
  · intro h
    rw [h, LinearMap.comp_zero]

/-- The projective coefficient ideal represents vanishing on every test algebra. -/
theorem baseChange_eq_zero_iff :
    f.baseChange A = 0 ↔ ideal f ≤ RingHom.ker (algebraMap R A) := by
  rw [← embedded_baseChange_eq_zero_iff f A]
  exact FreeTargetVanishing.baseChange_eq_zero_iff _ _ A

/-- The coefficient quotient kills the original map, not only its free-module image. -/
theorem quotient_baseChange_eq_zero : f.baseChange (R ⧸ ideal f) = 0 := by
  apply (baseChange_eq_zero_iff f _).mpr
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

end FLT.Mazur.ProjectiveTargetVanishing
