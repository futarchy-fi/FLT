/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.NumberTheory.Padics.PolynomialSpecialFiber
public import FLT.Mathlib.RingTheory.LocalizedRelationReduction

/-! # Comparing a p-adic presentation with its special-fibre presentation -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace PadicInt

open MvPolynomial

variable (p : ℕ) [Fact p.Prime] {σ A : Type*} [CommRing A] [Algebra ℤ_[p] A]

/-- Evaluation commutes with the polynomial and target special-fibre comparisons. -/
theorem modPEquivSpecialFiber_aeval (x : σ → A)
    (f : MvPolynomial σ ℤ_[p] ⧸ Ideal.span {algebraMap ℤ_[p] (MvPolynomial σ ℤ_[p]) (p : ℤ_[p])}) :
    modPEquivSpecialFiber p A ((aeval (R := ℤ_[p]) x).modPrincipal (p : ℤ_[p]) f) =
      aeval (R := ZMod p) (fun i ↦ (1 : ZMod p) ⊗ₜ[ℤ_[p]] x i) (polynomialModPEquiv p σ f) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  change modPEquivSpecialFiber p A (Ideal.Quotient.mk _ (aeval (R := ℤ_[p]) x f)) = _
  rw [modPEquivSpecialFiber_mk, polynomialModPEquiv_mk]
  have h : (Algebra.TensorProduct.includeRight : A →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] A).comp
      (aeval (R := ℤ_[p]) x) =
      ((aeval (R := ZMod p) (fun i ↦ (1 : ZMod p) ⊗ₜ[ℤ_[p]] x i)).restrictScalars ℤ_[p]).comp
        (mapAlgHom (Algebra.ofId ℤ_[p] (ZMod p))) := by
    ext i
    simp
  exact DFunLike.congr_fun h f

/-- A special-fibre coordinate surjection gives a surjection of principal reductions. -/
theorem modPrincipal_aeval_surjective (x : σ → A)
    (hx : Function.Surjective (aeval (R := ZMod p) (fun i ↦ (1 : ZMod p) ⊗ₜ[ℤ_[p]] x i))) :
    Function.Surjective ((aeval (R := ℤ_[p]) x).modPrincipal (p : ℤ_[p])) := by
  intro a
  obtain ⟨f, hf⟩ := hx (modPEquivSpecialFiber p A a)
  refine ⟨(polynomialModPEquiv p σ).symm f, (modPEquivSpecialFiber p A).injective ?_⟩
  rw [modPEquivSpecialFiber_aeval, AlgEquiv.apply_symm_apply, hf]

/-- The reduced relation ideal is the transport of the special-fibre polynomial kernel. -/
theorem ker_modPrincipal_aeval (x : σ → A) :
    RingHom.ker ((aeval (R := ℤ_[p]) x).modPrincipal (p : ℤ_[p])) =
      (RingHom.ker (aeval (R := ZMod p) (fun i ↦ (1 : ZMod p) ⊗ₜ[ℤ_[p]] x i))).map
        (polynomialModPEquiv p σ).symm.toRingHom := by
  erw [Ideal.map_comap_of_equiv (polynomialModPEquiv p σ).symm.toRingEquiv]
  ext f
  simp only [RingHom.mem_ker, Ideal.mem_comap]
  change ((aeval (R := ℤ_[p]) x).modPrincipal (p : ℤ_[p])) f = 0 ↔
    aeval (R := ZMod p) (fun i ↦ (1 : ZMod p) ⊗ₜ[ℤ_[p]] x i)
      (polynomialModPEquiv p σ f) = 0
  constructor
  · intro h
    exact (modPEquivSpecialFiber_aeval p x f).symm.trans (by rw [h, map_zero])
  · intro h
    apply (modPEquivSpecialFiber p A).injective
    exact (modPEquivSpecialFiber_aeval p x f).trans (h.trans (map_zero _).symm)

end PadicInt
