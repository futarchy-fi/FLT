/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedNormal
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Embeddings of unramified stages from residue embeddings

A residue embedding sends the reduction of an integral generator to a
simple root. Hensel lifts it, and the fraction-field power basis extends
the lifted root to a field embedding.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open Polynomial IsLocalRing

variable {R S T K L M : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Algebra.FormallyUnramified R S] [Finite (ResidueField R)]
  [Field L] [Algebra K L] [Algebra R L] [Algebra S L] [IsFractionRing S L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [CommRing T] [HenselianLocalRing T] [Algebra R T] [IsLocalHom (algebraMap R T)]
  [Field M] [Algebra K M] [Algebra R M] [Algebra T M]
  [IsScalarTower R K M] [IsScalarTower R T M]

/-- A residue embedding supplies a fraction-field embedding of an unramified stage. -/
theorem nonempty_algHom_of_residue_embedding
    (e : ResidueField S →ₐ[ResidueField R] ResidueField T) : Nonempty (L →ₐ[K] M) := by
  obtain ⟨P, t, hPm, hPi, hsep, ht, hgen, _⟩ :=
    exists_splitting_generator (R := R) (S := S)
  have hroot : aeval (residue S t) (P.map (residue R)) = 0 := by
    rw [← map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl, ht, map_zero]
  have he : aeval (e (residue S t)) (P.map (residue R)) = 0 := by
    rw [aeval_algHom_apply, hroot, map_zero]
  have hmaps : (P.map (algebraMap R T)).map (residue T) =
      (P.map (residue R)).map (algebraMap (ResidueField R) (ResidueField T)) := by
    rw [map_map, map_map]
    rfl
  have heval : ((P.map (algebraMap R T)).map (residue T)).IsRoot (e (residue S t)) := by
    rw [IsRoot.def, hmaps, eval_map_algebraMap]
    exact he
  have hder : ((P.map (algebraMap R T)).map (residue T)).derivative.eval
      (e (residue S t)) ≠ 0 := by
    rw [hmaps, derivative_map, eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero he
  obtain ⟨y, ⟨hy, _⟩, _⟩ := existsUnique_root_of_residue
    (P.map (algebraMap R T)) (hPm.map _) _ heval hder
  have hPiR : Irreducible P := hPm.irreducible_of_irreducible_map (residue R) P hPi
  have hPiK : Irreducible (P.map (algebraMap R K)) :=
    hPm.irreducible_iff_irreducible_map_fraction_map.mp hPiR
  have htK : aeval (algebraMap S L t) (P.map (algebraMap R K)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, ht, map_zero]
  have hmin : minpoly K (algebraMap S L t) = P.map (algebraMap R K) :=
    (minpoly.eq_of_irreducible_of_monic hPiK htK (hPm.map _)).symm
  have hint : IsIntegral K (algebraMap S L t) := ⟨_, hPm.map _, htK⟩
  let pb := PowerBasis.ofAdjoinSimpleEqTop hint (fraction_adjoin_eq_top (K := K) t hgen)
  refine ⟨pb.lift (algebraMap T M y) ?_⟩
  rw [show pb.gen = algebraMap S L t from PowerBasis.ofAdjoinSimpleEqTop_gen _ _,
    hmin, aeval_map_algebraMap, aeval_algebraMap_apply]
  simpa only [IsRoot.def, eval_map_algebraMap, map_zero] using congrArg (algebraMap T M) hy

/-- Residue-degree divisibility constructs an embedding between unramified stages. -/
theorem nonempty_algHom_of_residue_degree_dvd [Module.Finite R T]
    (h : Module.finrank (ResidueField R) (ResidueField S) ∣
      Module.finrank (ResidueField R) (ResidueField T)) : Nonempty (L →ₐ[K] M) := by
  let := ResidueField.finite_of_finite (R := R) (S := T) inferInstance
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd h
  exact nonempty_algHom_of_residue_embedding (K := K) (L := L) (M := M) e

end LocalClassFieldTheory
