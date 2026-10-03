/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedFiniteStageBaseChange
public import FLT.LocalClassFieldTheory.UnramifiedFrobeniusEmbedding

/-!
# Arithmetic Frobenius restriction across local base change

At every finite stage the new-base Frobenius acts by the residue-degree
power of the old-base Frobenius. The stage comparisons determine the
restriction on the entire unramified union.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L C : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S L C


attribute [local instance] stageDvr stageUnramified stageFractionRing stageFinite stageLocalHom

/-- At each actual finite stage, base-change restriction scales Frobenius by residue degree. -/
theorem unramifiedFrobenius_baseChange_stage (n : UnramifiedIndex) :
    (unramifiedBaseChangeRestriction R S K L C (unramifiedFrobenius S L C)).restrictNormal
        (unramifiedFiniteStage R K C n) =
      unramifiedStageFrobenius R K C n ^ Module.finrank (ResidueField R) (ResidueField S) := by
  let E := unramifiedFiniteStage R K C n
  let F := unramifiedFiniteStage S L C n
  let : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply R K C r
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply R S C r
  apply unramifiedFrobenius_embedding R S K L E F
    (unramifiedFiniteStageBaseChange R S K L C n)
  intro x
  have h := unramifiedFiniteStageBaseChange_action R S K L C n (unramifiedFrobenius S L C) x
  rw [unramifiedFrobenius_restrict] at h
  exact h

/-- The actual continuous Galois restriction sends Frobenius to its residue-degree power. -/
theorem unramifiedFrobenius_baseChange :
    unramifiedBaseChangeRestriction R S K L C (unramifiedFrobenius S L C) =
      unramifiedFrobenius R K C ^ Module.finrank (ResidueField R) (ResidueField S) := by
  apply (unramifiedDegreeLimitEquiv R K C).injective
  apply Subtype.ext
  funext n
  rw [unramifiedDegreeLimitEquiv_apply, unramifiedDegreeLimitEquiv_apply]
  change _ = (AlgEquiv.restrictNormalHom (unramifiedFiniteStage R K C n.unop))
    (unramifiedFrobenius R K C ^ _)
  rw [map_pow]
  change _ = ((unramifiedFrobenius R K C).restrictNormal _) ^ _
  rw [unramifiedFrobenius_restrict]
  exact unramifiedFrobenius_baseChange_stage R S K L C n.unop

end LocalClassFieldTheory
