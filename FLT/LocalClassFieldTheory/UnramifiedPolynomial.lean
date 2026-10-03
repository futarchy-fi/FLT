/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.HenselianRoots
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.Monogenic
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.UnramifiedSubalgebra
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# A splitting generator for an unramified Henselian DVR extension

Lift a primitive residue element. Unramifiedness puts a base uniformizer
in its generated algebra, and Nakayama gives generation of the whole DVR.
Finite residue fields make the lifted polynomial split by Hensel's lemma.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open Polynomial IsLocalRing

variable {R S : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Algebra.FormallyUnramified R S]

omit [HenselianLocalRing S] in
/-- A lifted residue generator generates the entire unramified DVR. -/
theorem adjoin_eq_top_of_residue_generator (t : S)
    (hgen : Algebra.adjoin (ResidueField R) {residue S t} = ⊤) :
    Algebra.adjoin R {t} = ⊤ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπS : Irreducible (algebraMap R S π) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S),
      hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  apply Subalgebra.eq_top_of_residue_surjective_of_irreducible _ ?_ hπS
    (Subalgebra.algebraMap_mem _ π)
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hgen
  intro s
  obtain ⟨p, hp⟩ := hgen (residue S s)
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue R) residue_surjective p
  refine ⟨⟨aeval t q, aeval_mem_adjoin_singleton R t⟩, ?_⟩
  change residue S (aeval t q) = residue S s
  rw [map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl, hq, hp]

/-- A finite unramified Henselian DVR with finite residue field has a monic
splitting polynomial and an integral root generating the whole ring. -/
theorem exists_splitting_generator [Finite (ResidueField R)] :
    ∃ (P : R[X]) (t : S), P.Monic ∧ Irreducible (P.map (residue R)) ∧
      (P.map (residue R)).Separable ∧ aeval t P = 0 ∧
      Algebra.adjoin R {t} = ⊤ ∧ (P.map (algebraMap R S)).Splits := by
  obtain ⟨P, t, hPm, hPi, _, ht, hgen⟩ :=
    existsUnramifiedResidueGenerator (R := R) (S := S)
  have hs : (P.map (residue R)).Separable := PerfectField.separable_of_irreducible hPi
  have hr : aeval (residue S t) (P.map (residue R)) = 0 := by
    rw [← map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl, ht, map_zero]
  have hmin : minpoly (ResidueField R) (residue S t) = P.map (residue R) :=
    (minpoly.eq_of_irreducible_of_monic hPi hr (hPm.map _)).symm
  let := ResidueField.finite_of_finite (R := R) (S := S) inferInstance
  have hsplit : ((P.map (residue R)).map
      (algebraMap (ResidueField R) (ResidueField S))).Splits := by
    rw [← hmin]
    exact Normal.splits (inferInstance : Normal (ResidueField R) (ResidueField S))
      (residue S t)
  have hmaps : (P.map (algebraMap R S)).map (residue S) =
      (P.map (residue R)).map (algebraMap (ResidueField R) (ResidueField S)) := by
    rw [map_map, map_map]
    rfl
  refine ⟨P, t, hPm, hPi, hs, ht, adjoin_eq_top_of_residue_generator t hgen, ?_⟩
  apply splits_of_separable_residue _ (hPm.map _)
  · rw [hmaps]
    exact hs.map
  · rwa [hmaps]

end LocalClassFieldTheory
