/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.RamificationInertia.Basic
public import FLT.GroupScheme.RaynaudStageHenselian
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Equal residue and fraction degrees imply unramifiedness

The local fundamental identity recovers the maximal-ideal equality omitted
from the residue-extension constructor's output. Completeness then passes
to its finite free integral ring.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra R S] [Module.Finite R S] [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsLocalHom (algebraMap R S)]

/-- Equality of residue and fraction degrees forces the maximal ideal to be extended. -/
theorem map_maximalIdeal_of_finrank_eq
    (hdeg : Module.finrank K L = Module.finrank (ResidueField R) (ResidueField S)) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    (by
      intro x y h
      apply FaithfulSMul.algebraMap_injective R L
      simpa only [← IsScalarTower.algebraMap_apply R S L] using
        congrArg (algebraMap S L) h)
  have : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have hp : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have h := Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing S hp
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R),
    IsIntegralClosure.rank R K L S, hdeg] at h
  have he : (maximalIdeal S).ramificationIdx R = 1 := by
    exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h.trans (one_mul _).symm)
  classical
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp]
  simp [IsLocalRing.primesOver_eq S hp, he]

/-- Separable residue and equality of degrees give formal unramifiedness. -/
theorem formallyUnramified_of_finrank_eq
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (hdeg : Module.finrank K L = Module.finrank (ResidueField R) (ResidueField S)) :
    Algebra.FormallyUnramified R S :=
  .of_map_maximalIdeal (map_maximalIdeal_of_finrank_eq R S K L hdeg)

/-- The ring in the residue-extension constructor is complete over a complete base. -/
theorem complete_of_finrank_eq [IsAdicComplete (maximalIdeal R) R]
    (hdeg : Module.finrank K L = Module.finrank (ResidueField R) (ResidueField S)) :
    IsAdicComplete (maximalIdeal S) S := by
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    (by
      intro x y h
      apply FaithfulSMul.algebraMap_injective R L
      simpa only [← IsScalarTower.algebraMap_apply R S L] using
        congrArg (algebraMap S L) h)
  exact RaynaudParameters.unramified_stage_complete
    (map_maximalIdeal_of_finrank_eq R S K L hdeg)

/-- The same constructed ring satisfies Hensel's lemma. -/
theorem henselian_of_finrank_eq [IsAdicComplete (maximalIdeal R) R]
    (hdeg : Module.finrank K L = Module.finrank (ResidueField R) (ResidueField S)) :
    HenselianLocalRing S := by
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    (by
      intro x y h
      apply FaithfulSMul.algebraMap_injective R L
      simpa only [← IsScalarTower.algebraMap_apply R S L] using
        congrArg (algebraMap S L) h)
  exact RaynaudParameters.unramified_stage_henselian
    (map_maximalIdeal_of_finrank_eq R S K L hdeg)

end LocalClassFieldTheory
