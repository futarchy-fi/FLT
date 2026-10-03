/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite unramified stages in a fixed algebraically closed field

Every finite separable residue extension lifts to a finite DVR embedded in
one fixed algebraically closed overfield. The original uniformizer generates
the new maximal ideal. This constructs finite stages, not their directed union.
-/

@[expose] public noncomputable section

universe u v

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace RaynaudParameters

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (Ω : Type v) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [FaithfulSMul R Ω]

/-- A prescribed finite separable residue extension has a finite unramified
DVR lift embedded in the common closure, with its original uniformizer. -/
theorem exists_embedded_unramified_stage {π : R} (hπ : Irreducible π)
    (k' : Type u) [Field k'] [Algebra (ResidueField R) k']
    [FiniteDimensional (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S) (_ : Module.Finite R S) (_ : IsLocalHom (algebraMap R S))
      (f : S →ₐ[R] Ω), Function.Injective f ∧ Irreducible (algebraMap R S π) ∧
        maximalIdeal S = (maximalIdeal R).map (algebraMap R S) ∧
        Nonempty (ResidueField S ≃ₐ[ResidueField R] k') := by
  obtain ⟨p, hpm, -, hpi, hdeg, ⟨e⟩⟩ :=
    Field.exists_monic_irreducible_adjoinRoot_algEquiv (ResidueField R) k'
  obtain ⟨P, hPm, hP, hPdeg⟩ := exists_monic_map_residue_eq hpm
  have hred : Irreducible (P.map (residue R)) := hP ▸ hpi
  have hirr : Irreducible P := hPm.irreducible_of_irreducible_map (residue R) P hred
  have hpos : 0 < P.natDegree := by rw [hPdeg, hdeg]; exact Module.finrank_pos
  have hdeg0 : P.degree ≠ 0 := (natDegree_pos_iff_degree_pos.mp hpos).ne'
  let S := AdjoinRoot P
  let instDomain : IsDomain S := AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  obtain ⟨hmax, instDvr, instLocal⟩ :=
    AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hPm hdeg0 hred
  let instFinite : Module.Finite R S := hPm.finite_adjoinRoot
  have hm : maximalIdeal S = (maximalIdeal R).map (algebraMap R S) :=
    (eq_maximalIdeal hmax).symm
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_aeval_eq_zero Ω P hdeg0
  let f : S →ₐ[R] Ω := AdjoinRoot.liftAlgHom P (Algebra.ofId R Ω) t ht
  have hinj : Function.Injective f :=
    injective_of_not_maximalIdeal_le_ker f.toRingHom fun hle ↦ by
      have h := hle (hm.symm ▸ Ideal.mem_map_of_mem (algebraMap R S) hπ.not_isUnit)
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, f.commutes] at h
      exact hπ.ne_zero ((FaithfulSMul.algebraMap_injective R Ω) (by simpa using h))
  have hπS : Irreducible (algebraMap R S π) := by
    apply (irreducible_iff_uniformizer _).mpr
    rw [hm, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let : Algebra R k' := ((algebraMap (ResidueField R) k').comp (residue R)).toAlgebra
  let : IsScalarTower R (ResidueField R) k' := .of_algebraMap_eq fun _ ↦ rfl
  let e' : ResidueField S ≃ₐ[R] k' :=
    (AdjoinRoot.residueFieldEquiv hm).trans
      ((Ideal.quotientEquivAlgOfEq R (congrArg (fun q ↦ Ideal.span {q}) hP)).trans
        (e.restrictScalars R))
  exact ⟨S, inferInstance, instDomain, instDvr, inferInstance, instFinite, instLocal,
    f, hinj, hπS, hm, ⟨e'.extendScalarsOfSurjective residue_surjective⟩⟩

end RaynaudParameters
