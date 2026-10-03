/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedDegree
public import FLT.Mathlib.RingTheory.Unramified.LocalRing

/-!
# Complete unramified realizations of finite residue extensions

The existing residue-extension constructor yields an integral closure,
formally unramified and complete at its maximal ideal, hence Henselian.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Realize a finite separable residue extension by a complete unramified integral DVR. -/
theorem exists_complete_unramified_extension
    (k' : Type u) [Field k'] [Algebra (ResidueField R) k']
    [FiniteDimensional (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u)
      (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L) (_ : IsFractionRing S L)
      (_ : IsLocalHom (algebraMap R S)),
      IsIntegralClosure S R L ∧ Algebra.FormallyUnramified R S ∧
      IsAdicComplete (maximalIdeal S) S ∧ HenselianLocalRing S ∧
      Module.finrank K L = Module.finrank (ResidueField R) k'
        ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] k') := by
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, hdeg, ⟨e⟩⟩ :=
    exists_unramified_extension_of_residueField (R := R) (K := K) k'
  have : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    Algebra.IsSeparable.of_algHom (ResidueField R) k' e.toAlgHom
  have hd : Module.finrank K L = Module.finrank (ResidueField R) (ResidueField S) :=
    hdeg.trans e.toLinearEquiv.finrank_eq.symm
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsIntegralClosure.of_isIntegrallyClosed S R L,
    formallyUnramified_of_finrank_eq R S K L hd,
    complete_of_finrank_eq R S K L hd, henselian_of_finrank_eq R S K L hd, hdeg, ⟨e⟩⟩

end LocalClassFieldTheory
