/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeRestriction
public import FLT.LocalClassFieldTheory.UnramifiedStageFrobenius

/-!
# Embeddings of degree-indexed stages across base change

The existing containment theorem gives actual embeddings between finite
stages inside the two unions. Their Galois actions commute with restriction.
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


/-- Base change embeds each reindexed finite stage into the new stage of the same degree. -/
def unramifiedFiniteStageBaseChange (n : UnramifiedIndex) :
    unramifiedFiniteStage R K C n →ₐ[K] unramifiedFiniteStage S L C n where
  toFun x := ⟨maximalUnramifiedBaseChange R S K L C x.val,
    (mem_unramifiedFiniteStage S L C n _).mpr
      (unramifiedStage_baseChange R S K L C n.degree
        ((mem_unramifiedFiniteStage R K C n x.val).mp x.property))⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The embeddings of stages and unions commute with their actual restricted actions. -/
theorem unramifiedFiniteStageBaseChange_action (n : UnramifiedIndex) (g : Gal(B/L))
    (x : unramifiedFiniteStage R K C n) :
    unramifiedFiniteStageBaseChange R S K L C n
        ((unramifiedBaseChangeRestriction R S K L C g).restrictNormal
          (unramifiedFiniteStage R K C n) x) =
      (g.restrictNormal (unramifiedFiniteStage S L C n))
        (unramifiedFiniteStageBaseChange R S K L C n x) := by
  apply Subtype.ext
  change maximalUnramifiedBaseChange R S K L C
      (algebraMap (unramifiedFiniteStage R K C n) A
        ((unramifiedBaseChangeRestriction R S K L C g).restrictNormal _ x)) =
    algebraMap (unramifiedFiniteStage S L C n) B
      (g.restrictNormal _ (unramifiedFiniteStageBaseChange R S K L C n x))
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes]
  exact unramifiedBaseChangeRestriction_apply R S K L C g x.val

end LocalClassFieldTheory
