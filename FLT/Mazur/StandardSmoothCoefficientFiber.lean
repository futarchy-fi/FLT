/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalLocalizationCartier
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Local equations in coefficient fibers of standard smooth curves

A finite quotient remains finite after any field-valued coefficient change.
Its actual extended ideal has a regular generator in every local localization
of the coefficient fiber. Neither the original base nor the field map is
required to be Noetherian or flat.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.FCurve

variable {R B K : Type u} [CommRing R] [CommRing B] [Field K]
  [Algebra R B] [Algebra R K]

/-- The actual extended ideal has a finite quotient in every field coefficient fiber. -/
theorem finite_field_fiber_quotient (I : Ideal B) [Module.Finite R (B ⧸ I)] :
    Module.Finite K ((K ⊗[R] B) ⧸
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) := by
  exact Module.Finite.equiv (Algebra.TensorProduct.tensorQuotientEquiv K B K I).toLinearEquiv

/-- Localizations of a smooth curve's coefficient fiber have regular ideal equations. -/
theorem regular_generator_field_fiber_localization
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (I : Ideal B) [Module.Finite R (B ⧸ I)]
    (M : Submonoid (K ⊗[R] B)) (L : Type u) [CommRing L]
    [Algebra (K ⊗[R] B) L] [IsLocalRing L] [IsLocalization M L] :
    ∃ a : L, IsRegular a ∧
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := K))).map
        (algebraMap (K ⊗[R] B) L) = Ideal.span {a} := by
  let J := I.map (Algebra.TensorProduct.includeRight (R := R) (A := K))
  let _ : Module.Finite K ((K ⊗[R] B) ⧸ J) := finite_field_fiber_quotient I
  let _ : IsArtinianRing ((K ⊗[R] B) ⧸ J) :=
    IsArtinianRing.of_finite K ((K ⊗[R] B) ⧸ J)
  exact regular_generator_local_localization (K := K) M J

end FLT.Mazur.FCurve
