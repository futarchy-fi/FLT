/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedDifferentials
public import FLT.Mazur.AdicSeparatedDerivation

/-!
# Extending original derivations into separated completed-ring modules

Finite original differentials permit extension to the completed algebra.
For separated targets restriction and extension are inverse, including when
the target was constructed using a different formal presentation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicDerivationExtension

variable {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing A] [Module.Finite A Ω[A⁄R]]
  (I : Ideal A) [AddCommGroup N] [Module R N] [Module A N]
  [Module (AdicCompletion I A) N] [IsScalarTower R A N]
  [IsScalarTower R (AdicCompletion I A) N] [IsScalarTower A (AdicCompletion I A) N]

/-- Extend an original derivation using completed original differentials. -/
def extend (d : Derivation R A N) : Derivation R (AdicCompletion I A) N :=
  (AdicFiniteModuleLift.lift I d.liftKaehlerDifferential).compDer
    (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I)

/-- Extension preserves every original value. -/
@[simp] theorem extend_of (d : Derivation R A N) (a : A) :
    extend I d (AdicCompletion.of I A a) = d a := by
  change AdicFiniteModuleLift.lift I d.liftKaehlerDifferential
    (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I
      (AdicCompletion.of I A a)) = _
  rw [AdicDerivationFiltration.completion_of, AdicFiniteModuleLift.lift_of,
    Derivation.liftKaehlerDifferential_comp_D]

/-- Restricting an extended derivation recovers the original derivation. -/
@[simp] theorem extend_compAlgebraMap (d : Derivation R A N) :
    (extend I d).compAlgebraMap A = d := by
  ext a
  exact extend_of I d a

/-- Separation makes restriction to original sections injective. -/
theorem extend_unique [IsHausdorff I N] (d : Derivation R A N)
    (e : Derivation R (AdicCompletion I A) N)
    (h : ∀ a, e (AdicCompletion.of I A a) = d a) : e = extend I d := by
  apply AdicSeparatedDerivation.ext_of I I.fg_of_isNoetherianRing
  intro a
  rw [h, extend_of]

/-- Derivations into a separated completed-ring module are unchanged by completing the source. -/
def equiv [IsHausdorff I N] :
    Derivation R A N ≃ Derivation R (AdicCompletion I A) N where
  toFun := extend I
  invFun d := d.compAlgebraMap A
  left_inv := extend_compAlgebraMap I
  right_inv d := (extend_unique I _ d fun _ ↦ rfl).symm

end FLT.Mazur.AdicDerivationExtension
