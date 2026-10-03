/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexTiltGalois
public import FLT.PadicHodgeTheory.ComplexFontaineTheta

/-! # Equivariance of the actual sharp map -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Reduction identifies multiplicative compatible p-power sequences uniquely. -/
theorem complexGalois_quotientMulEquiv (σ : PadicGalois p)
    (x : Perfection 𝓞_ℂ_[p] p) :
    Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})
        (Perfection.mapMonoidHom p (complexIntegerGalois p σ).toMonoidHom x) =
      complexTiltGalois p σ
        (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}) x) := by
  apply Perfection.ext
  intro n
  rfl

/-- The multiplicative inverse-Frobenius lift commutes with Galois. -/
theorem complexGalois_quotientMulEquiv_symm (σ : PadicGalois p) (x : IntegralTilt p) :
    Perfection.mapMonoidHom p (complexIntegerGalois p σ).toMonoidHom
        ((Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).symm x) =
      (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).symm
        (complexTiltGalois p σ x) := by
  apply (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).injective
  rw [complexGalois_quotientMulEquiv]
  exact (congrArg (complexTiltGalois p σ)
    ((Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).apply_symm_apply x)).trans
      ((Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).apply_symm_apply
        (complexTiltGalois p σ x)).symm

/-- Sharp intertwines the actual tilt and integer-ring actions. -/
theorem complexSharp_equivariant (σ : PadicGalois p) (x : IntegralTilt p) :
    complexSharp p (complexTiltGalois p σ x) =
      complexIntegerGalois p σ (complexSharp p x) := by
  have h := congrArg (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0)
    (complexGalois_quotientMulEquiv_symm p σ x)
  have hc (y : IntegralTilt p) : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0
      ((Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).symm y) =
        complexSharp p y := Perfection.coeff_zero_symm_quotientMulEquiv y
  rw [Perfection.coeffMonoidHom_mapMonoidHom, hc, hc] at h
  exact h.symm

end PadicHodgeTheory
