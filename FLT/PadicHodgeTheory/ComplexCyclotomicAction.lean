/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.CyclotomicCharacterNaturality
public import FLT.PadicHodgeTheory.ComplexCyclotomicTilt
public import FLT.PadicHodgeTheory.ComplexSharpEquivariance

/-! # Cyclotomic action on the actual compatible roots -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The completed Galois automorphism is the extension already constructed. -/
def complexGaloisEquiv (σ : PadicGalois p) : ℂ_[p] ≃+* ℂ_[p] :=
  MulSemiringAction.toRingEquiv (PadicGalois p) ℂ_[p] σ

/-- Completion preserves the actual p-adic cyclotomic character. -/
theorem complexCyclotomicCharacter_eq (σ : PadicGalois p) :
    cyclotomicCharacter ℂ_[p] p (complexGaloisEquiv p σ) =
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv := by
  symm
  apply cyclotomicCharacter.naturality p (algebraMap (PadicAlgCl p) ℂ_[p])
  intro x
  exact (complexGalois_coe p σ x).symm

/-- Each actual integral root transforms by the corresponding cyclotomic residue. -/
theorem complexCyclotomicSequence_action (σ : PadicGalois p) (n : ℕ) :
    complexIntegerGalois p σ ((complexCyclotomicSequence p).val n) =
      (complexCyclotomicSequence p).val n ^
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val.toZModPow n).val := by
  apply Subtype.ext
  have h := cyclotomicCharacter.spec p (complexGaloisEquiv p σ)
    ((complexCyclotomicSequence p).val n : ℂ_[p])
    (congrArg Subtype.val (complexCyclotomicSequence_primitive p n).pow_eq_one)
  rw [complexCyclotomicCharacter_eq] at h
  exact h

/-- The multiplicative lift of the transformed epsilon has the cyclotomic coordinates. -/
theorem complexCyclotomicTilt_action_lift (σ : PadicGalois p) (n : ℕ) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n
      ((Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).symm
        (complexTiltGalois p σ (complexCyclotomicTilt p))) =
      (complexCyclotomicSequence p).val n ^
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val.toZModPow n).val := by
  rw [← complexGalois_quotientMulEquiv_symm, Perfection.coeffMonoidHom_mapMonoidHom,
    complexCyclotomicTilt_lift]
  exact complexCyclotomicSequence_action p σ n

end PadicHodgeTheory
