/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDerivationExtension

/-!
# Completed original differentials with arbitrary separated targets

The universal property holds for every separated module over the completed
ring, including modules whose construction uses another formal presentation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSeparatedDifferentials

variable {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing A] [Module.Finite A Ω[A⁄R]]
  (I : Ideal A) [AddCommGroup N] [Module R N] [Module A N]
  [Module (AdicCompletion I A) N] [IsScalarTower R A N]
  [IsScalarTower R (AdicCompletion I A) N] [IsScalarTower A (AdicCompletion I A) N]

/-- Factor a completed derivation through the completion of original differentials. -/
def lift (d : Derivation R (AdicCompletion I A) N) :
    AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] N :=
  AdicFiniteModuleLift.lift I (d.compAlgebraMap A).liftKaehlerDifferential

omit [IsScalarTower R (AdicCompletion I A) N] in
/-- The factorization retains differentials of every original section. -/
@[simp] theorem lift_of_D (d : Derivation R (AdicCompletion I A) N) (a : A) :
    lift I d (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a)) =
      d (AdicCompletion.of I A a) := by
  rw [lift, AdicFiniteModuleLift.lift_of, Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- Separation identifies the factorization on every completed section. -/
theorem lift_comp [IsHausdorff I N] (d : Derivation R (AdicCompletion I A) N) :
    (lift I d).compDer
      (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I) = d := by
  apply AdicSeparatedDerivation.ext_of I I.fg_of_isNoetherianRing
  intro a
  change lift I d (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I
    (AdicCompletion.of I A a)) = _
  rw [AdicDerivationFiltration.completion_of, lift_of_D]

/-- The universal factorization is unique even without separation of the target. -/
theorem lift_unique (d : Derivation R (AdicCompletion I A) N)
    (f : AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] N)
    (hf : f.compDer
      (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I) = d) :
    f = lift I d := by
  apply AdicFiniteModuleExt.ext_differentials I
  intro a
  rw [lift_of_D]
  have he := Derivation.congr_fun hf (AdicCompletion.of I A a)
  change f (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I
    (AdicCompletion.of I A a)) = _ at he
  rwa [AdicDerivationFiltration.completion_of] at he

/-- Completed original differentials represent derivations into all separated targets. -/
def equiv [IsHausdorff I N] :
    (AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] N) ≃
      Derivation R (AdicCompletion I A) N where
  toFun f := f.compDer (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I)
  invFun := lift I
  left_inv f := (lift_unique I _ f rfl).symm
  right_inv := lift_comp I

end FLT.Mazur.AdicSeparatedDifferentials
