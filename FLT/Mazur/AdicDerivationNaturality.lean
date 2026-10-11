/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDerivationCompletion
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Naturality of completed original derivations

Completion commutes with a linear map on the original target module.
In particular every completed original derivation factors through the
completion of the original module of relative differentials.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicDerivationFiltration

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  (d : Derivation R A M) (I : Ideal A) (f : M →ₗ[A] N)

/-- Finite derivatives commute with a linear map on the original target. -/
theorem quotientMap_comp (n : ℕ) (a : A ⧸ I ^ (n + 1)) :
    quotientMap (f.compDer d) I n a =
      f.reduceModIdeal (I ^ n) (quotientMap d I n a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- The completed original derivation is natural in its target module. -/
theorem completion_comp_apply (a : AdicCompletion I A) :
    completion (f.compDer d) I a = AdicCompletion.map I f (completion d I a) := by
  apply AdicCompletion.ext
  intro n
  exact quotientMap_comp d I f n (AdicCompletion.evalₐ I (n + 1) a)

/-- Every completed original derivation factors through completed original differentials. -/
theorem completion_liftKaehlerDifferential (a : AdicCompletion I A) :
    AdicCompletion.map I d.liftKaehlerDifferential
        (completion (KaehlerDifferential.D R A) I a) = completion d I a := by
  rw [← completion_comp_apply, d.liftKaehlerDifferential_comp]

end FLT.Mazur.AdicDerivationFiltration
