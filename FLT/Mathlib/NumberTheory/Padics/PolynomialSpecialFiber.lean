/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.NumberTheory.Padics.SpecialFiber
public import FLT.Mathlib.RingTheory.MvPolynomial.LocalizedReduction
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Polynomial presentations on the special fibre of a p-adic algebra -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PadicInt

open MvPolynomial

variable (p : ℕ) [Fact p.Prime] (σ : Type*)

/-- Reduction of a polynomial ring over the p-adic integers is the polynomial
ring over the prime field. -/
def polynomialModPEquiv :
    (MvPolynomial σ ℤ_[p] ⧸ Ideal.span {C (p : ℤ_[p])}) ≃ₐ[ℤ_[p]]
      MvPolynomial σ (ZMod p) :=
  (Ideal.quotientEquivAlgOfEq ℤ_[p] (by
    rw [Ideal.map_span, Set.image_singleton])).trans
    ((quotientEquivQuotientMvPolynomial (Ideal.span {(p : ℤ_[p])})).symm.trans
      (mapAlgEquiv σ (modPEquivZMod p)))

/-- Polynomial reduction reduces each coefficient. -/
@[simp] theorem polynomialModPEquiv_mk (f : MvPolynomial σ ℤ_[p]) :
    polynomialModPEquiv p σ (Ideal.Quotient.mk _ f) = map toZMod f := by
  simp only [polynomialModPEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    quotientEquivQuotientMvPolynomial_symm_mk, mapAlgEquiv_apply, map_map]
  rfl

/-- The reduction of any localization of a p-adic polynomial ring is a
localization of the polynomial ring over the prime field. -/
def localizedPolynomialModPEquiv (M : Submonoid (MvPolynomial σ ℤ_[p])) :
    (Localization M ⧸ Ideal.span {algebraMap ℤ_[p] (Localization M) (p : ℤ_[p])}) ≃ₐ[ℤ_[p]]
      Localization (M.map (map (toZMod (p := p)))) := by
  let e := mapAlgEquiv σ (modPEquivZMod p)
  let N := M.map (map (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])})))
  have hN : N.map e.toRingHom = M.map (map (toZMod (p := p))) := by
    ext y
    simp only [Submonoid.mem_map]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change map toZMod x = map (modPEquivZMod p).toRingHom
        (map (Ideal.Quotient.mk _) x)
      rw [map_map]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨map (Ideal.Quotient.mk _) x, ⟨x, hx, rfl⟩, ?_⟩
      change map (modPEquivZMod p).toRingHom (map (Ideal.Quotient.mk _) x) = map toZMod x
      rw [map_map]
      rfl
  exact (localizedModPrincipalEquiv (p : ℤ_[p]) M).trans
    (IsLocalization.algEquivOfAlgEquiv (Localization N)
      (Localization (M.map (map (toZMod (p := p))))) e hN)

/-- The localized comparison agrees with coefficient reduction on the source ring. -/
theorem localizedPolynomialModPEquiv_mk
    (M : Submonoid (MvPolynomial σ ℤ_[p])) (f : MvPolynomial σ ℤ_[p]) :
    localizedPolynomialModPEquiv p σ M
      (Ideal.Quotient.mk _ (algebraMap _ (Localization M) f)) =
    algebraMap _ (Localization (M.map (map (toZMod (p := p))))) (map toZMod f) := by
  simp only [localizedPolynomialModPEquiv, AlgEquiv.trans_apply,
    localizedModPrincipalEquiv_mk, IsLocalization.algEquivOfAlgEquiv_eq,
    mapAlgEquiv_apply, map_map]
  rfl

end PadicInt
