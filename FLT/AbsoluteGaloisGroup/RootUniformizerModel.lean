/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.RootInertiaTransitivity
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.EisensteinExtension

/-!
# Constructed finite root-uniformizer models

A root of a uniformizer of any positive degree has a finite integral DVR
model of exactly that degree. The root equation and ramification index are
proved from the Eisenstein polynomial. This does not assert that the model
is Galois or identify it with an arbitrary finite character splitting field.
-/

@[expose] public noncomputable section
open Polynomial IsLocalRing
namespace LocalRoot
universe u v
variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Construct the finite field and its integral closure with a root uniformizer. -/
theorem exists_root_uniformizer_model {π : R} (hπ : Irreducible π)
    {n : ℕ} (hn : 0 < n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (_ : Algebra R E) (_ : IsScalarTower R K E) (S : Type u) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S E) (_ : IsScalarTower R S E)
      (_ : IsFractionRing S E) (_ : IsIntegralClosure S R E) (y : S),
      Module.finrank K E = n ∧ Irreducible y ∧ y ^ n = algebraMap R S π ∧
        IsDiscreteValuationRing.addVal S (algebraMap R S π) = (n : ℕ∞) ∧
        Algebra.adjoin R {y} = ⊤ := by
  obtain ⟨E, hE, hKE, hfin, hRE, htK, S, hS, hdom, hdvr, hRS, hmod,
    hSE, htS, hfrac, hint, y, hdeg, hy, heq, hval, hgen⟩ :=
    (uniformizer_binomial_eisenstein hπ hn).existsTotallyRamifiedExtension
      (K := K) (monic_X_pow_sub_C π hn.ne') (by simpa using hn) hπ
  refine ⟨E, hE, hKE, hfin, hRE, htK, S, hS, hdom, hdvr, hRS, hmod,
    hSE, htS, hfrac, hint, y, ?_, hy, ?_, ?_, hgen⟩
  · simpa using hdeg
  · simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using heq
  · simpa using hval

/-- An integral binomial model embeds into a specified
overfield, carrying its uniformizer to the specified root. -/
theorem exists_embedded_root_uniformizer_model
    (Ω : Type v) [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω]
    {π : R} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    {α : Ω} (hα : α ^ n = algebraMap R Ω π) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S) (_ : Module.Finite R S) (y : S) (f : S →ₐ[R] Ω),
      Irreducible y ∧ y ^ n = algebraMap R S π ∧ f y = α ∧
        Function.Injective f ∧ Algebra.adjoin R {y} = ⊤ := by
  let P : R[X] := X ^ n - C π
  have hm : P.Monic := monic_X_pow_sub_C π hn.ne'
  have he : P.IsEisensteinAt (maximalIdeal R) := uniformizer_binomial_eisenstein hπ hn
  have hd : 0 < P.natDegree := by simpa [P] using hn
  have hi : Irreducible P := he.irreducible inferInstance hm.isPrimitive hd
  let S := AdjoinRoot P
  let : IsDomain S := AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi)
  obtain ⟨hdvr, hy⟩ := AdjoinRoot.isDiscreteValuationRingOfEisenstein he hm hd
  let : Module.Finite R S := hm.finite_adjoinRoot
  have hz : aeval α P = 0 := by simp [P, hα]
  let f : S →ₐ[R] Ω := AdjoinRoot.liftAlgHom P (Algebra.ofId R Ω) α hz
  have hf : f (AdjoinRoot.root P) = α := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hα0 : α ≠ 0 := by
    intro h
    have hz' : algebraMap R Ω π = 0 := by simpa [h, hn.ne'] using hα.symm
    exact hπ.ne_zero ((FaithfulSMul.algebraMap_injective R Ω) (by simpa using hz'))
  have hinj : Function.Injective f :=
    IsDiscreteValuationRing.injective_of_not_maximalIdeal_le_ker f.toRingHom fun hle ↦ by
      have h := hle hy.not_isUnit
      exact hα0 (hf.symm.trans h)
  refine ⟨S, inferInstance, inferInstance, hdvr, inferInstance, inferInstance,
    AdjoinRoot.root P, f, hy, ?_, hf, hinj, AdjoinRoot.adjoinRoot_eq_top⟩
  have h : aeval (AdjoinRoot.root P) P = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simpa only [P, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h

end LocalRoot
