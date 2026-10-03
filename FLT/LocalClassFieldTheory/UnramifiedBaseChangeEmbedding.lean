/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUniqueness

/-!
# Embedding unramified stages after a finite local base extension

Residue degrees multiply in the integral tower. An unramified extension
of the new base with sufficiently divisible degree therefore contains an
embedding of the original unramified stage, by the proved Hensel lifting theorem.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable {R S K L E F : Type u}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  [Field F] [Algebra L F] [Algebra S F] [IsScalarTower S L F]
  [Algebra K F] [Algebra R F] [IsScalarTower R K F]
  [IsScalarTower R S F] [Finite (ResidueField R)]
  [Algebra.IsSeparable K E] [Algebra.IsSeparable L F]

/-- Degree divisibility constructs an embedding even when the base extension is ramified. -/
theorem unramifiedBaseChangeEmbedding (hE : IsUnramifiedStage R K E)
    (hF : IsUnramifiedStage S L F) (h : Module.finrank K E ∣ Module.finrank L F) :
    Nonempty (E →ₐ[K] F) := by
  obtain ⟨_, A, _, _, _, _, _, _, _, _, _, huA, hhA⟩ := hE
  obtain ⟨_, B, _, _, _, _, _, _, _, _, _, huB, hhB⟩ := hF
  let := huA
  let := hhA
  let := huB
  let := hhB
  let : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R B F := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S F, IsScalarTower.algebraMap_apply S B F]
    rfl
  let : Module.Finite R B := Module.Finite.trans S B
  let : IsLocalHom (algebraMap R B) :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
      ((FaithfulSMul.algebraMap_injective S B).comp (FaithfulSMul.algebraMap_injective R S))
  have hdA := finrank_eq_of_formallyUnramified R A K E
  have hdB := finrank_eq_of_formallyUnramified S B L F
  apply nonempty_algHom_of_residue_degree_dvd (R := R) (S := A) (T := B)
  rw [← hdA, ← Module.finrank_mul_finrank (ResidueField R) (ResidueField S) (ResidueField B),
    ← hdB]
  exact dvd_mul_of_dvd_right h _

end LocalClassFieldTheory
