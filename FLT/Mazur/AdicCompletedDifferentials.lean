/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDerivationNaturality
public import FLT.Mazur.AdicDerivationUniqueness
public import FLT.Mazur.AdicFiniteModuleLift

/-!
# Universal property of completed original differentials

The completion of the original module of relative differentials represents
relative derivations on the completed algebra with values in completed
original modules. This retains the original cotangent module and does not
identify it with ordinary algebraic differentials of the completed ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedDifferentials

open AdicDerivationFiltration

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing A] [Module.Finite A Ω[A⁄R]]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (I : Ideal A)

/-- Original relative scalars agree with the completed-ring action on completed modules. -/
instance relativeScalarTower :
    IsScalarTower R (AdicCompletion I A) (AdicCompletion I M) :=
  IsScalarTower.of_algebraMap_smul fun r m ↦ by
    rw [IsScalarTower.algebraMap_apply R A (AdicCompletion I A),
      algebraMap_smul, algebraMap_smul]

/-- Factor a completed-algebra derivation through completed original differentials. -/
def lift (d : Derivation R (AdicCompletion I A) (AdicCompletion I M)) :
    AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] AdicCompletion I M :=
  AdicFiniteModuleLift.lift I (d.compAlgebraMap A).liftKaehlerDifferential

/-- On an original differential the factorization is the given derivative. -/
@[simp] theorem lift_of_D
    (d : Derivation R (AdicCompletion I A) (AdicCompletion I M)) (a : A) :
    lift I d (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a)) =
      d (AdicCompletion.of I A a) := by
  rw [lift, AdicFiniteModuleLift.lift_of, Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- The factorization recovers the derivation on every completed section. -/
theorem lift_comp (d : Derivation R (AdicCompletion I A) (AdicCompletion I M)) :
    (lift I d).compDer (completion (KaehlerDifferential.D R A) I) = d := by
  apply completion_ext I I.fg_of_isNoetherianRing
  intro a
  change lift I d (completion (KaehlerDifferential.D R A) I
    (AdicCompletion.of I A a)) = _
  rw [completion_of, lift_of_D]

/-- The factorization is uniquely determined by the completed universal derivative. -/
theorem lift_unique (d : Derivation R (AdicCompletion I A) (AdicCompletion I M))
    (f : AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] AdicCompletion I M)
    (hf : f.compDer (completion (KaehlerDifferential.D R A) I) = d) : f = lift I d := by
  apply AdicFiniteModuleExt.ext_differentials I
  intro a
  rw [lift_of_D]
  have h := Derivation.congr_fun hf (AdicCompletion.of I A a)
  change f (completion (KaehlerDifferential.D R A) I (AdicCompletion.of I A a)) = _ at h
  rwa [completion_of] at h

/-- Completed original differentials represent derivations to completed original modules. -/
def linearMapEquivDerivation :
    (AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] AdicCompletion I M) ≃
      Derivation R (AdicCompletion I A) (AdicCompletion I M) where
  toFun f := f.compDer (completion (KaehlerDifferential.D R A) I)
  invFun := lift I
  left_inv f := (lift_unique I _ f rfl).symm
  right_inv := lift_comp I

end FLT.Mazur.AdicCompletedDifferentials
