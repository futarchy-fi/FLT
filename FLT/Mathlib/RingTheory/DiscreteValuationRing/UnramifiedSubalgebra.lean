/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Unramified coefficient rings inside Henselian DVR extensions

A primitive separable residue element lifts by Hensel's lemma to a root of
a monic polynomial with irreducible reduction. Its polynomial quotient is
an unramified discrete valuation ring mapping into the original extension.
-/

@[expose] public noncomputable section

universe u

open Polynomial IsLocalRing

namespace IsLocalRing

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S]
  [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]

omit [IsDomain S] [IsDiscreteValuationRing S] in
/-- A separable residue generator lifts to an exact root of a monic
polynomial with irreducible reduction. -/
theorem existsUnramifiedResidueGenerator :
    ∃ (P : R[X]) (t : S), P.Monic ∧ Irreducible (P.map (residue R)) ∧
      0 < P.natDegree ∧ aeval t P = 0 ∧
      Algebra.adjoin (ResidueField R) {residue S t} = ⊤ := by
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element (ResidueField R) (ResidueField S)
  have hβint : IsIntegral (ResidueField R) β := Algebra.IsIntegral.isIntegral β
  obtain ⟨P, hPm, hP, hdeg⟩ := exists_monic_map_residue_eq (minpoly.monic hβint)
  obtain ⟨x, hx⟩ := residue_surjective (R := S) β
  have heval (z : S) (f : R[X]) :
      residue S (aeval z f) = aeval (residue S z) (f.map (residue R)) :=
    map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl f z
  have hfx : aeval x P ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, heval, hP, hx]
    exact minpoly.aeval _ _
  have hd : IsUnit (aeval x P.derivative) := by
    rw [← residue_ne_zero_iff_isUnit, heval, ← derivative_map, hP, hx]
    exact (Algebra.IsSeparable.isSeparable (ResidueField R) β).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  obtain ⟨t, ht, htx⟩ := HenselianLocalRing.is_henselian
    (P.map (algebraMap R S)) (hPm.map _) x
    (by simpa using hfx) (by simpa only [derivative_map, eval_map_algebraMap] using hd)
  have hres : residue S t = β := by
    rw [← hx, ← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr htx
  refine ⟨P, t, hPm, hP ▸ minpoly.irreducible hβint,
    hdeg ▸ minpoly.natDegree_pos hβint, ?_, ?_⟩
  · simpa [Polynomial.IsRoot] using ht
  · rw [hres,
      ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite _ _),
      hβ, IntermediateField.top_toSubalgebra]

end IsLocalRing

namespace IsDiscreteValuationRing

variable {R S : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]

omit [IsDiscreteValuationRing S] in
/-- A finite Henselian DVR extension with separable residue extension contains
an unramified coefficient DVR with the same residue field as the extension. -/
theorem existsUnramifiedCoefficientRing {π : R} (hπ : Irreducible π) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : Algebra R C) (_ : Module.Finite R C) (_ : Algebra C S)
      (_ : IsScalarTower R C S),
      Function.Injective (algebraMap C S) ∧ Irreducible (algebraMap R C π) ∧
        ∀ s : S, ∃ c : C, residue S (algebraMap C S c) = residue S s := by
  obtain ⟨P, t, hPm, hPi, hdeg, ht, hgen⟩ :=
    IsLocalRing.existsUnramifiedResidueGenerator (R := R) (S := S)
  have hPirr : Irreducible P := hPm.irreducible_of_irreducible_map (residue R) P hPi
  have hPdeg : P.degree ≠ 0 := (natDegree_pos_iff_degree_pos.mp hdeg).ne'
  let C := AdjoinRoot P
  let instDomain : IsDomain C :=
    AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hPirr)
  obtain ⟨hmaximal, instDvr, instLocal⟩ :=
    AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hPm hPdeg hPi
  let instFinite : Module.Finite R C := hPm.finite_adjoinRoot
  let f : C →ₐ[R] S := AdjoinRoot.liftAlgHom P (Algebra.ofId R S) t ht
  let algCS : Algebra C S := f.toRingHom.toAlgebra
  have halg : algebraMap C S = f.toRingHom := RingHom.algebraMap_toAlgebra _
  let instTower : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg]
    exact (f.commutes r).symm
  have hmax : maximalIdeal C = (maximalIdeal R).map (algebraMap R C) :=
    (eq_maximalIdeal hmaximal).symm
  have hinj : Function.Injective (algebraMap C S) :=
    injective_of_not_maximalIdeal_le_ker _ fun hle => by
      have h := hle (hmax.symm ▸ Ideal.mem_map_of_mem (algebraMap R C) hπ.not_isUnit)
      rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply R C S] at h
      exact hπ.ne_zero (FaithfulSMul.algebraMap_injective R S (by simpa using h))
  have hπC : Irreducible (algebraMap R C π) := by
    apply (irreducible_iff_uniformizer _).mpr
    rw [hmax, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  refine ⟨C, inferInstance, instDomain, instDvr, inferInstance, instFinite,
    algCS, instTower, hinj, hπC, ?_⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hgen
  intro s
  obtain ⟨p, hp⟩ := hgen (residue S s)
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue R) residue_surjective p
  refine ⟨AdjoinRoot.mk P q, ?_⟩
  have heval : algebraMap C S (AdjoinRoot.mk P q) = aeval t q := by
    rw [halg]
    rfl
  rw [heval, map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl, hq, hp]

end IsDiscreteValuationRing
