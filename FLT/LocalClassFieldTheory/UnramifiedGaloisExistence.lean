/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedExistence
public import FLT.LocalClassFieldTheory.UnramifiedNormal
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.Field.ULift

/-!
# Galois unramified stages of every positive degree

Normality upgrades the complete residue-extension realization to a Galois
stage. Finite-field extensions supply every positive degree.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K]


variable [Finite (ResidueField R)]

/-- A finite residue extension lifts to a Galois unramified stage. -/
theorem exists_galois_unramified_extension
    (k' : Type u) [Field k'] [Algebra (ResidueField R) k']
    [FiniteDimensional (ResidueField R) k'] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u)
      (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L) (_ : IsFractionRing S L)
      (_ : IsLocalHom (algebraMap R S)),
      IsIntegralClosure S R L ∧ Algebra.FormallyUnramified R S ∧
      IsAdicComplete (maximalIdeal S) S ∧ HenselianLocalRing S ∧
      Module.finrank K L = Module.finrank (ResidueField R) k'
        ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] k') := by
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, hc, hu, hcomp, hh, hd, he⟩ :=
    exists_complete_unramified_extension (R := R) (K := K) k'
  let := hu
  let := hh
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro x y h
    apply FaithfulSMul.algebraMap_injective R L
    simpa only [← IsScalarTower.algebraMap_apply R S L] using congrArg (algebraMap S L) h)
  let : Normal K L := normal_of_unramified (R := R) (S := S)
  let : IsGalois K L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hc, hu, hcomp, hh, hd, he⟩

/-- There is a Galois unramified stage of each positive degree. -/
theorem exists_galois_unramified_degree (n : ℕ) [NeZero n] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u)
      (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L) (_ : IsFractionRing S L)
      (_ : IsLocalHom (algebraMap R S)),
      IsIntegralClosure S R L ∧ Algebra.FormallyUnramified R S ∧
      IsAdicComplete (maximalIdeal S) S ∧ HenselianLocalRing S ∧
      Module.finrank K L = n := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField R)
  let : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField R) p⟩
  let k' := ULift.{u} (FiniteField.Extension (ResidueField R) p n)
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, hc, hu, hcomp, hh, hd, _⟩ :=
    exists_galois_unramified_extension (R := R) (K := K) k'
  have hk : Module.finrank (ResidueField R) k' = n :=
    (ULift.moduleEquiv.finrank_eq).trans (FiniteField.finrank_extension (ResidueField R) p n)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hc, hu, hcomp, hh, hd.trans hk⟩

end LocalClassFieldTheory
