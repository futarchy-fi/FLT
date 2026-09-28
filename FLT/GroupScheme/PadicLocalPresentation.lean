/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalHopfPresentation
public import FLT.Mathlib.NumberTheory.Padics.PresentationReduction
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Minimal localized presentations of finite flat local p-adic Hopf algebras

Minimal coordinates on the Hopf special fibre lift to algebra generators by
Nakayama. The special-fibre square relation theorem supplies the relations,
and flatness lifts those relations after localization at the maximal ideal.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

open MvPolynomial

variable (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [HopfAlgebra ℤ_[p] A]

/-- The cotangent dimension at the identity of the Hopf special fibre. -/
abbrev padicSpecialFiberCotangentDimension : ℕ :=
  Module.finrank (ZMod p)
    (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((ZMod p) ⊗[ℤ_[p]] A))).Cotangent

variable [IsLocalRing A] [Module.Finite ℤ_[p] A] [Module.Flat ℤ_[p] A]

/-- A finite flat local commutative Hopf algebra over the p-adic integers is a
quotient of a localized polynomial ring by exactly the special-fibre cotangent
dimension many relations, with the same number of polynomial coordinates. -/
theorem exists_minimal_local_padic_presentation :
    ∃ P : Algebra.Generators ℤ_[p] A (Fin (padicSpecialFiberCotangentDimension p A)),
      let f := aeval (R := ℤ_[p]) P.val
      ∃ (g : Fin (padicSpecialFiberCotangentDimension p A) → f.localizedSource)
        (e : (f.localizedSource ⧸ Ideal.span (Set.range g)) ≃ₐ[ℤ_[p]] A),
        ∀ s, e (Ideal.Quotient.mk _ s) = f.localizeAtMaximal s := by
  let B := (ZMod p) ⊗[ℤ_[p]] A
  let q : A →ₐ[ℤ_[p]] B := Algebra.TensorProduct.includeRight
  have hq : Function.Surjective q :=
    Algebra.TensorProduct.includeRight_surjective A (ZMod.ringHom_surjective PadicInt.toZMod)
  let : Nontrivial B := Bialgebra.nontrivial (ZMod p)
  let : IsLocalRing B := IsLocalRing.of_surjective' q.toRingHom hq
  obtain ⟨P, _, r, hr⟩ := exists_minimal_square_presentation (k := ZMod p) (A := B) p
  choose x hx using fun i ↦ hq (P.val i)
  have hx' : (fun i ↦ (1 : ZMod p) ⊗ₜ[ℤ_[p]] x i) = P.val := funext hx
  let f := aeval (R := ℤ_[p]) x
  have hfbar : Function.Surjective (f.modPrincipal (p : ℤ_[p])) :=
    PadicInt.modPrincipal_aeval_surjective p x (by rw [hx']; exact P.aeval_val_surjective)
  have hpj : (p : ℤ_[p]) ∈ Ideal.jacobson (⊥ : Ideal ℤ_[p]) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hf : Function.Surjective f := f.surjective_of_modPrincipal (p : ℤ_[p]) hpj hfbar
  let eP := PadicInt.polynomialModPEquiv p (Fin (padicSpecialFiberCotangentDimension p A))
  have hrel : Ideal.span (Set.range (fun i ↦ eP.symm (r i))) =
      RingHom.ker (f.modPrincipal (p : ℤ_[p])) := by
    rw [PadicInt.ker_modPrincipal_aeval, hx', hr, Ideal.map_span, ← Set.range_comp]
    rfl
  let : FaithfulSMul ℤ_[p] A := (faithfulSMul_iff_algebraMap_injective ℤ_[p] A).mpr
    (Bialgebra.algebraMap_injective A)
  have hpA : algebraMap ℤ_[p] A (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal A := by
    apply map_nonunit (algebraMap ℤ_[p] A)
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hp : IsRegular (p : ℤ_[p]) :=
    isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  obtain ⟨g, e, he⟩ :=
    f.exists_localized_quotient_equiv_of_flat_of_reduced_relations hf hp hpA _ hrel
  exact ⟨Algebra.Generators.ofSurjective x hf, g, e, he⟩

end HopfAlgebra
