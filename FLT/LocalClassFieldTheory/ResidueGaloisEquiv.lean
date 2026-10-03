/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ResidueActionFaithful
public import FLT.LocalClassFieldTheory.ResidueActionSurjective
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Galois comparison for an unramified integral DVR extension

For a finite Galois extension of fraction fields, with formally unramified
integral closure a DVR, reduction is an equivalence. Finiteness, freeness,
invariance, and the power basis are derived from these arithmetic hypotheses.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]

/-- Restrict a field automorphism to the integral closure, then reduce. -/
def residueGaloisAction : Gal(L/K) →*
    (ResidueField S ≃ₐ[ResidueField R] ResidueField S) :=
  (residueAction R S).comp (galRestrict R K L S).toMonoidHom

omit [IsFractionRing S L] [FiniteDimensional K L] in
/-- The field reduction map uses the actual integral restriction. -/
@[simp] theorem residueGaloisAction_apply_residue (σ : Gal(L/K)) (x : S) :
    residueGaloisAction R S K L σ (residue S x) =
      residue S (galRestrict R K L S σ x) := rfl

/-- Surjectivity follows from Galois invariance of the integral closure. -/
theorem residueGaloisAction_surjective :
    Function.Surjective (residueGaloisAction R S K L) := by
  let : Finite (S ≃ₐ[R] S) := Finite.of_equiv Gal(L/K) (galRestrict R K L S).toEquiv
  let := Algebra.isInvariant_of_isGalois' R K L S
  exact (residueAction_surjective R S).comp (galRestrict R K L S).surjective

variable [Algebra.FormallyUnramified R S]

omit [IsFractionRing S L] in
/-- Faithfulness follows from the constructed integral power basis and its
unit derivative, without assuming that inertia is trivial. -/
theorem residueGaloisAction_injective :
    Function.Injective (residueGaloisAction R S K L) := by
  let := IsIntegralClosure.finite R K L S
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  let := IsIntegralClosure.module_free R K L S
  exact (residueAction_injective R S).comp (galRestrict R K L S).injective

/-- The residue Galois equivalence of a finite unramified integral DVR extension. -/
def residueGaloisEquiv : Gal(L/K) ≃*
    (ResidueField S ≃ₐ[ResidueField R] ResidueField S) :=
  MulEquiv.ofBijective (residueGaloisAction R S K L)
    ⟨residueGaloisAction_injective R S K L, residueGaloisAction_surjective R S K L⟩

/-- The equivalence is reduction, including on chosen representatives. -/
@[simp] theorem residueGaloisEquiv_apply_residue (σ : Gal(L/K)) (x : S) :
    residueGaloisEquiv R S K L σ (residue S x) =
      residue S (galRestrict R K L S σ x) := rfl

end LocalClassFieldTheory
